from pathlib import Path
import subprocess
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional

from src.dataset.helpers import CoqBlockParser

class DependencyGraphBuilder:
    """
    This class is responsible for building and reading the .dpd file,
    and creating a directed graph from it.
    """

    def __init__(
        self,
        coq_file: Path,
        out_dpd_path: Optional[Path] = None
    ) -> None:
        """
        :param coq_file: Path to the Coq file (e.g., AnyFile.v).
        :param out_dpd_path: Desired final location for the .dpd file.
        """
        self.coq_file = coq_file
        self.base_name = self.coq_file.stem  # Dynamically infer the filename without extension

        # If not provided, default to `src/dependency_graph/{base_name}.dpd`
        if out_dpd_path is None:
            script_dir = Path(__file__).parent.resolve()
            default_dir = script_dir.parent / "dependency_graph"
            default_dir.mkdir(parents=True, exist_ok=True)
            self.out_dpd_path = default_dir / f"{self.base_name}.dpd"
        else:
            self.out_dpd_path = out_dpd_path

        # Will hold node and edge data once parsed
        self.nodes: Dict[str, Dict[str, str]] = {}
        self.edges: List[Tuple[str, str]] = []

    def build_dependency_graph(self) -> None:
        """
        1. Create a helper .v file in the same folder as the target .v file.
        2. Invoke `coqc` to generate the .dpd dependency file.
        3. Move or rename the generated .dpd file to the desired out_dpd_path.
        """
        coq_dir = self.coq_file.parent
        graph_file = coq_dir / f"{self.base_name}Graph.v"
        dpd_filename = f"{self.base_name}.dpd"

        # The minimal text needed to generate the .dpd graph 
        everything_graph_content = f"""\
        Require dpdgraph.dpdgraph.                              
        From LF Require {self.base_name}.

        Set DependGraph File "{dpd_filename}".
        Print FileDependGraph {self.base_name}.
        """
        # LF is hardcoded should not cause issues though

        # 1) Write {base_name}Graph.v
        graph_file.write_text(everything_graph_content, encoding="utf-8")

        # 2) Compile {base_name}Graph.v using coqc
        subprocess.run(
            [
                "coqc",
                "-Q", str(coq_dir), "LF",
                str(graph_file.name)
            ],
            cwd=coq_dir,
            check=True
        )

        # 3) The above command should produce {base_name}.dpd in coq_dir
        generated_dpd = coq_dir / dpd_filename
        if not generated_dpd.exists():
            raise FileNotFoundError(f"Could not find generated {generated_dpd} after coqc.")

        # Move it to out_dpd_path (rename() handles moves)
        self.out_dpd_path.parent.mkdir(parents=True, exist_ok=True)
        generated_dpd.rename(self.out_dpd_path)

        print(f"Dependency graph built: {self.out_dpd_path}")

    def parse_dpd_file(self) -> None:
        """
        Parse the .dpd file (assumed to be at self.out_dpd_path) into self.nodes and self.edges.
        """
        if not self.out_dpd_path.exists():
            raise FileNotFoundError(
                f"Cannot parse .dpd file. {self.out_dpd_path} does not exist."
            )
        with self.out_dpd_path.open('r', encoding='utf-8') as file:
            for line in file:
                line = line.strip()
                if line.startswith("N:"):
                    parts = line.split(maxsplit=3)
                    node_id: str = parts[1]
                    label: str = parts[2].strip('"')
                    attributes: str = parts[3] if len(parts) > 3 else ""
                    self.nodes[node_id] = {
                        "label": label,
                        "attributes": attributes
                    }
                elif line.startswith("E:"):
                    parts = line.split()
                    self.edges.append((parts[1], parts[2]))

    def create_graph(self) -> nx.DiGraph:
        """
        Create a directed graph (nx.DiGraph) from parsed .dpd data.
        """
        graph = nx.DiGraph()
        for node_id, data in self.nodes.items():
            graph.add_node(node_id, **data)
        graph.add_edges_from(self.edges)
        return graph


class CoqDataProcessor:
    """
    This class encapsulates the entire data processing flow:
      1. Build the dependency graph (dpd file).
      2. Read the Coq file and parse into blocks.
      3. Parse the .dpd file and create a DiGraph.
      4. Merge block info with graph info.
      5. Write final JSON output.
    """

    def __init__(
        self,
        coq_file: Path,
        out_json_file: Path,
        dpd_output_path: Optional[Path] = None,
    ) -> None:
        """
        :param coq_file: Path to EverythingLF.v
        :param out_json_file: Where to save the final JSON
        :param dpd_output_path: Where to place EverythingLF.dpd
        """
        self.coq_file = coq_file
        self.out_json_file = out_json_file
        self.dpd_output_path = dpd_output_path

    @staticmethod
    def get_label(text: str) -> str:
        """
        Get the second whitespace-delimited token from a string,
        removing a trailing ":" if present.
        """
        if not text:
            return ""
        tokens = text.split()
        if len(tokens) < 2:
            return ""
        return tokens[1].replace(":", "")

    def process(self) -> None:
        """
        Main pipeline:
        1. Build the dependency graph (generates EverythingLF.dpd).
        2. Read Coq file content and parse into blocks.
        3. Parse the .dpd file and build a NetworkX DiGraph.
        4. Merge block DataFrame with graph info.
        5. Write final JSON.
        """
        # 1) Build the .dpd dependency graph file
        dp_builder = DependencyGraphBuilder(
            coq_file=self.coq_file,
            out_dpd_path=self.dpd_output_path
        )
        dp_builder.build_dependency_graph()

        # 2) Read Coq file content and parse into blocks
        coq_content = self.coq_file.read_text(encoding="utf-8")
        blocks = CoqBlockParser.get_coq_blocks(coq_content)
        df = pd.DataFrame([{"Type": b["type"], "Chunk": b["raw"]} for b in blocks])

        # 3) Parse the .dpd file and create a DiGraph
        dp_builder.parse_dpd_file()
        graph = dp_builder.create_graph()

        # 4) Merge block DataFrame with graph info
        #    Add a 'Label' column from the second token of the chunk's first line
        df["Label"] = df["Chunk"].apply(self.get_label)

        # Create a simple DataFrame from the graph data
        graph_data = []
        for node, attributes in graph.nodes(data=True):
            graph_data.append({
                "GraphNodeId": node,
                "GraphLabel": attributes.get("label", "")
            })
        df_graph = pd.DataFrame(graph_data)

        # Merge on Label <--> GraphLabel
        merged_df = df.merge(
            df_graph,
            left_on="Label",
            right_on="GraphLabel",
            how="left"
        )

        # For each row, gather the labels of its successors
        def get_dependencies_labels(node_id: str) -> Optional[List[str]]:
            if pd.isna(node_id):
                return None
            successors = list(graph.successors(node_id))
            if not successors:
                return None
            return [graph.nodes[s]["label"] for s in successors]

        merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(get_dependencies_labels)

        # Drop helper columns
        columns_to_drop = ["Label", "GraphNodeId", "GraphLabel"]
        merged_df.drop(columns=columns_to_drop, inplace=True)

        # 5) Save to JSON
        merged_df.to_json(
            self.out_json_file,
            orient="records",
            indent=2,
            force_ascii=False
        )
        print(f"Done. Final JSON saved to: {self.out_json_file}")


def main() -> None:
    """
    Example of a main function:
      - Points to EverythingLF.v
      - Sets default JSON output path
      - Runs the CoqDataProcessor pipeline
    """
    script_dir = Path(__file__).parent.resolve()
    # Where your EverythingLF.v is located
    coq_file = script_dir / "single_file_data" / "lf" / "EverythingLF.v"
    # Desired final JSON output
    out_json_file = script_dir / "processed_data" / "df.json"
    # If you want to override the dpd location:
    # dpd_output_path = script_dir.parent / "dependency_graph" / "EverythingLF.dpd"
    # Otherwise let it default to src/dependency_graph/EverythingLF.dpd

    processor = CoqDataProcessor(
        coq_file=coq_file,
        out_json_file=out_json_file,
        # dpd_output_path=dpd_output_path   # or omit for default
    )
    processor.process()


if __name__ == "__main__":
    main()
