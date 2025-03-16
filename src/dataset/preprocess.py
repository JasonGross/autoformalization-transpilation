from pathlib import Path
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional
from helpers import get_coq_blocks

def parseDpdFile(filePath: Path) -> Tuple[Dict[str, Dict[str, str]], List[Tuple[str, str]]]:
    """
    Parse a .dpd file into nodes and edges for the dependency graph.
    Returns (nodes_dict, edges_list).
    """
    nodes: Dict[str, Dict[str, str]] = {}
    edges: List[Tuple[str, str]] = []

    with filePath.open('r', encoding='utf-8') as file:
        for line in file:
            line = line.strip()
            if line.startswith("N:"):
                parts = line.split(maxsplit=3)
                nodeId: str = parts[1]
                label: str = parts[2].strip('"')
                attributes: str = parts[3] if len(parts) > 3 else ""
                nodes[nodeId] = {"label": label, "attributes": attributes}
            elif line.startswith("E:"):
                parts = line.split()
                source: str = parts[1]
                target: str = parts[2]
                edges.append((source, target))

    return nodes, edges


def createGraphFromDpd(filePath: Path) -> nx.DiGraph:
    """
    Creates a directed graph (nx.DiGraph) from parsed .dpd data.
    """
    nodes, edges = parseDpdFile(filePath)
    G = nx.DiGraph()
    for nodeId, data in nodes.items():
        G.add_node(nodeId, **data)
    G.add_edges_from(edges)
    return G


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


def main() -> None:
    """
    Main pipeline:
      1. Read `EverythingLF.v` content
      2. Parse it into blocks (helpers.get_coq_blocks)
      3. Create dependency graph from `EverythingLF.dpd`
      4. Merge block info with graph info by matching identifiers
      5. Output final JSON as `df.json`
    """
    
    script_dir = Path(__file__).parent.resolve()

    coq_file = script_dir / "single_file_data" / "lf" / "EverythingLF.v"
    dpd_file = script_dir.parent / "dependency_graph" / "EverythingLF.dpd"
    out_file = script_dir / "processed_data" / "df.json"


    # 1. Read Coq file content & parse into blocks
    coq_content = coq_file.read_text(encoding="utf-8")
    blocks = get_coq_blocks(coq_content)

    # 2. Create DataFrame of block data
    df = pd.DataFrame([{"Type": b["type"], "Chunk": b["raw"]} for b in blocks])

    # 3. Create dependency graph from DPD file
    G = createGraphFromDpd(dpd_file)

    # 4. Extract label from each chunk's second word
    df["Label"] = df["Chunk"].apply(get_second_word)

    # 5. Prepare a separate DataFrame of graph node labels``
    graph_data = []
    for node, attributes in G.nodes(data=True):
        graph_data.append({
            "GraphNodeId": node,
            "GraphLabel": attributes.get("label", "")
        })
    df_graph = pd.DataFrame(graph_data)

    # 6. Merge block DataFrame with graph info by matching labels
    merged_df = df.merge(df_graph, left_on="Label", right_on="GraphLabel", how="left")

    # 7. For each matched node, gather the labels of its direct successors (dependencies)
    def get_dependencies_labels(node_id: str) -> Optional[List[str]]:
        if pd.isna(node_id):
            return None
        successors = list(G.successors(node_id))
        if not successors:
            return None
        return [G.nodes[s]["label"] for s in successors]

    merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(get_dependencies_labels)

    # 8. Drop columns we no longer need
    columns_to_drop = ["Label", "GraphNodeId", "GraphLabel"]
    merged_df.drop(columns=columns_to_drop, inplace=True)

    # 9. Output final JSON
    merged_df.to_json(out_file, orient="records", indent=2, force_ascii=False)
    print(f"Done. Final JSON saved to: {out_file}")


if __name__ == "__main__":
    main()
