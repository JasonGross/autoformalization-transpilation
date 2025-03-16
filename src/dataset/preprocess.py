from pathlib import Path
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional

# Import our new parser class
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
                    self.nodes[node_id] = {"label": label, "attributes": attributes}
                elif line.startswith("E:"):
                    parts = line.split()
                    source: str = parts[1]
                    target: str = parts[2]
                    self.edges.append((source, target))

    def create_graph(self) -> nx.DiGraph:
        """
        Creates a directed graph (nx.DiGraph) from the data read in parse_dpd_file().
        """
        G = nx.DiGraph()
        for node_id, data in self.nodes.items():
            G.add_node(node_id, **data)
        G.add_edges_from(self.edges)
        return G


class CoqDataProcessor:
    """
    This class encapsulates the entire data processing flow:
      1. Reading the Coq file and parsing into blocks
      2. Creating a dependency graph
      3. Merging block info with graph info
      4. Writing final JSON output
    """

    def __init__(self, coq_file: Path, dpd_file: Path, out_file: Path) -> None:
        self.coq_file = coq_file
        self.dpd_file = dpd_file
        self.out_file = out_file

    @staticmethod
    def get_second_word(text: str) -> str:
        """
        Gets the second whitespace-delimited token from a string,
        removing trailing ":" if present.
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
          1. Read Coq file content & parse into blocks
          2. Create DataFrame of block data
          3. Create dependency graph from DPD file
          4. Merge block DataFrame with graph info
          5. Write final JSON
        """

        # 1. Read Coq file content & parse into blocks
        coq_content = self.coq_file.read_text(encoding="utf-8")
        blocks = CoqBlockParser.get_coq_blocks(coq_content)

        # 2. Create DataFrame of block data
        df = pd.DataFrame([{"Type": b["type"], "Chunk": b["raw"]} for b in blocks])

        # 3. Create dependency graph from DPD file
        dp_builder = DependencyGraphBuilder(self.dpd_file)
        dp_builder.parse_dpd_file()
        G = dp_builder.create_graph()

        # 4. Merge block DataFrame with graph info
        # 4.1 Extract label from each chunk's second word
        df["Label"] = df["Chunk"].apply(self.get_second_word)

        # 4.2 Prepare a separate DataFrame of graph node labels
        graph_data = []
        for node, attributes in G.nodes(data=True):
            graph_data.append({
                "GraphNodeId": node,
                "GraphLabel": attributes.get("label", "")
            })
        df_graph = pd.DataFrame(graph_data)

        # 4.3 Merge block DataFrame with graph info by matching labels
        merged_df = df.merge(df_graph, left_on="Label", right_on="GraphLabel", how="left")

        # 4.4 For each matched node, gather the labels of its direct successors (dependencies)
        def get_dependencies_labels(node_id: str) -> Optional[List[str]]:
            if pd.isna(node_id):
                return None
            successors = list(G.successors(node_id))
            if not successors:
                return None
            return [G.nodes[s]["label"] for s in successors]

        merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(get_dependencies_labels)

        # 5. Drop columns we no longer need and output final JSON
        columns_to_drop = ["Label", "GraphNodeId", "GraphLabel"]
        merged_df.drop(columns=columns_to_drop, inplace=True)

        merged_df.to_json(self.out_file, orient="records", indent=2, force_ascii=False)
        print(f"Done. Final JSON saved to: {self.out_file}")


def main() -> None:
    """
    Instantiates the processor and runs the pipeline.
    """
    script_dir = Path(__file__).parent.resolve()

    coq_file = script_dir / "single_file_data" / "lf" / "EverythingLF.v"
    dpd_file = script_dir.parent / "dependency_graph" / "EverythingLF.dpd"
    out_file = script_dir / "processed_data" / "df.json"

    processor = CoqDataProcessor(coq_file, dpd_file, out_file)
    processor.process()


if __name__ == "__main__":
    main()
