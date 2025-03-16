from pathlib import Path
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional

from helpers import CoqBlockParser


class DependencyGraphBuilder:
    """
    This class is responsible for reading and parsing .dpd files,
    and creating a directed graph from them.
    """

    def __init__(self, file_path: Path) -> None:
        self.file_path = file_path
        self.nodes: Dict[str, Dict[str, str]] = {}
        self.edges: List[Tuple[str, str]] = []

    def parse_dpd_file(self) -> None:
        """
        Parse a .dpd file into self.nodes and self.edges.
        """
        with self.file_path.open('r', encoding='utf-8') as file:
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
                    source: str = parts[1]
                    target: str = parts[2]
                    self.edges.append((source, target))

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
      1. Read the Coq file and parse into blocks.
      2. Create a dependency graph.
      3. Merge block info with graph info.
      4. Write final JSON output.
    """

    def __init__(
        self,
        coq_file: Path,
        dpd_file: Path,
        out_file: Path
    ) -> None:
        self.coq_file = coq_file
        self.dpd_file = dpd_file
        self.out_file = out_file

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
        1. Read Coq file content and parse into blocks.
        2. Create a DataFrame of block data.
        3. Create a dependency graph from the DPD file.
        4. Merge block DataFrame with graph info.
        5. Write final JSON.
        """
        coq_content = self.coq_file.read_text(encoding="utf-8")
        blocks = CoqBlockParser.get_coq_blocks(coq_content)
        df = pd.DataFrame([{"Type": b["type"], "Chunk": b["raw"]} for b in blocks])

        dp_builder = DependencyGraphBuilder(self.dpd_file)
        dp_builder.parse_dpd_file()
        graph = dp_builder.create_graph()

        df["Label"] = df["Chunk"].apply(self.get_label)

        graph_data = []
        for node, attributes in graph.nodes(data=True):
            graph_data.append({
                "GraphNodeId": node,
                "GraphLabel": attributes.get("label", "")
            })
        df_graph = pd.DataFrame(graph_data)

        merged_df = df.merge(
            df_graph,
            left_on="Label",
            right_on="GraphLabel",
            how="left"
        )

        def get_dependencies_labels(node_id: str) -> Optional[List[str]]:
            if pd.isna(node_id):
                return None
            successors = list(graph.successors(node_id))
            if not successors:
                return None
            return [graph.nodes[s]["label"] for s in successors]

        merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(
            get_dependencies_labels
        )

        columns_to_drop = ["Label", "GraphNodeId", "GraphLabel"]
        merged_df.drop(columns=columns_to_drop, inplace=True)

        merged_df.to_json(
            self.out_file,
            orient="records",
            indent=2,
            force_ascii=False
        )
        print(f"Done. Final JSON saved to: {self.out_file}")


def main() -> None:
    """
    Instantiate the processor and run the pipeline.
    """
    script_dir = Path(__file__).parent.resolve()
    coq_file = script_dir / "single_file_data" / "lf" / "EverythingLF.v"
    dpd_file = script_dir.parent / "dependency_graph" / "EverythingLF.dpd"
    out_file = script_dir / "processed_data" / "df.json"

    processor = CoqDataProcessor(coq_file, dpd_file, out_file)
    processor.process()


if __name__ == "__main__":
    main()
