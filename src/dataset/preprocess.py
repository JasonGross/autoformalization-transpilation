import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import networkx as nx
import pandas as pd

from src.dataset.helpers import CoqBlockParser


class DependencyGraphBuilder:
    """
    Builds and reads the .dpd file, creating a directed graph.
    """

    def __init__(self, coq_file: Path, out_dpd_path: Optional[Path] = None) -> None:
        self.coq_file = coq_file
        self.base_name = self.coq_file.stem

        if out_dpd_path is None:
            script_dir = Path(__file__).parent.resolve()
            default_dir = script_dir.parent / "dependency_graph"
            default_dir.mkdir(parents=True, exist_ok=True)
            self.out_dpd_path = default_dir / f"{self.base_name}.dpd"
        else:
            self.out_dpd_path = out_dpd_path

        self.nodes: Dict[str, Dict[str, str]] = {}
        self.edges: List[Tuple[str, str]] = []

    def build_dependency_graph(self) -> None:
        """
        1. Create a helper .v file for the target .v file.
        2. Invoke 'coqc' to generate the .dpd file.
        3. Move/rename it to self.out_dpd_path.
        """
        coq_dir = self.coq_file.parent
        graph_file = coq_dir / f"{self.base_name}Graph.v"
        dpd_filename = f"{self.base_name}.dpd"

        everything_graph_content = f"""
            Require dpdgraph.dpdgraph.
            From LF Require {self.base_name}.

            Set DependGraph File "{dpd_filename}".
            Print FileDependGraph {self.base_name}.
        """.strip()

        graph_file.write_text(everything_graph_content, encoding="utf-8")

        subprocess.run(
            ["coqc", "-Q", str(coq_dir), "LF", str(graph_file.name)],
            cwd=coq_dir,
            check=True
        )

        generated_dpd = coq_dir / dpd_filename
        if not generated_dpd.exists():
            raise FileNotFoundError(f"Could not find generated {generated_dpd} after coqc.")

        self.out_dpd_path.parent.mkdir(parents=True, exist_ok=True)
        generated_dpd.rename(self.out_dpd_path)
        print(f"Dependency graph built: {self.out_dpd_path}")

    def parse_dpd_file(self) -> None:
        """
        Parse the .dpd file into self.nodes and self.edges.
        """
        if not self.out_dpd_path.exists():
            raise FileNotFoundError(f"Cannot parse .dpd file. {self.out_dpd_path} does not exist.")

        with self.out_dpd_path.open('r', encoding='utf-8') as file:
            for line in file:
                line = line.strip()
                if line.startswith("N:"):
                    parts = line.split(maxsplit=3)
                    node_id = parts[1]
                    label = parts[2].strip('"')
                    attributes = parts[3] if len(parts) > 3 else ""
                    self.nodes[node_id] = {
                        "label": label,
                        "attributes": attributes
                    }
                elif line.startswith("E:"):
                    parts = line.split()
                    self.edges.append((parts[1], parts[2]))

    def create_graph(self) -> nx.DiGraph:
        """
        Create a directed graph from parsed .dpd data.
        """
        graph = nx.DiGraph()
        for node_id, data in self.nodes.items():
            graph.add_node(node_id, **data)
        graph.add_edges_from(self.edges)
        return graph


class CoqDataProcessor:
    """
    Overall data processing:
    - Build the dependency graph (.dpd file).
    - Read and parse the Coq file.
    - Parse the .dpd file into a graph.
    - Merge block info with graph info.
    - Write final JSON output.
    """

    def __init__(
        self,
        coq_file: Path,
        out_json_file: Path,
        dpd_output_path: Optional[Path] = None
    ) -> None:
        self.coq_file = coq_file
        self.out_json_file = out_json_file
        self.dpd_output_path = dpd_output_path

    @staticmethod
    def get_label(text: str) -> str:
        """
        Extract the second whitespace-delimited token, stripping trailing colons.
        For example, 'Example test_andb32:' -> 'test_andb32'.
        """
        tokens = text.split()
        if len(tokens) > 1:
            return tokens[1].replace(":", "")
        return ""

    def process(self) -> None:
        """
        Main pipeline: build graph, parse blocks, parse .dpd, merge,
        and output JSON.
        """
        dp_builder = DependencyGraphBuilder(
            self.coq_file,
            self.dpd_output_path
        )
        dp_builder.build_dependency_graph()

        coq_content = self.coq_file.read_text(encoding="utf-8")
        blocks = CoqBlockParser.get_coq_blocks(coq_content)
        df = pd.DataFrame(blocks)

        # Create a 'Label' column for merging with the dpd graph info.
        df["Label"] = df["Chunk"].apply(self.get_label)

        dp_builder.parse_dpd_file()
        graph = dp_builder.create_graph()

        # Build a dataframe of graph nodes and labels.
        graph_data = [
            {"GraphNodeId": node, "GraphLabel": attrs.get("label", "")}
            for node, attrs in graph.nodes(data=True)
        ]
        df_graph = pd.DataFrame(graph_data)

        # Merge by matching Coq block 'Label' with graph 'GraphLabel'
        merged_df = df.merge(
            df_graph,
            left_on="Label",
            right_on="GraphLabel",
            how="left"
        )

        def get_dependencies(node_id: str) -> Optional[List[str]]:
            if pd.isna(node_id):
                return None
            successors = list(graph.successors(node_id))
            if not successors:
                return None
            return [graph.nodes[s]["label"] for s in successors]

        merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(get_dependencies)
        merged_df.rename(columns={"Label": "Name"}, inplace=True)
        merged_df.drop(columns=["GraphNodeId", "GraphLabel"], inplace=True)

        merged_df.loc[merged_df["Type"] == "Other", "Name"] = None

        # Output to JSON.
        merged_df.to_json(
            self.out_json_file,
            orient="records",
            indent=2,
            force_ascii=False
        )
        print(f"Done. Final JSON saved to: {self.out_json_file}")


def main() -> None:
    """
    Example main entry point.
    """
    script_dir = Path(__file__).parent.resolve()
    coq_file = script_dir / "single_file_data" / "lf" / "EverythingLF.v"
    out_json_file = script_dir / "processed_data" / "df.json"

    processor = CoqDataProcessor(coq_file, out_json_file)
    processor.process()


if __name__ == "__main__":
    main()
