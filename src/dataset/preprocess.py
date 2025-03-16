import os
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional
from helpers import (
    formatCoqFile,
    extractBlocksFromPreprocessed
)

def parseDpdFile(filePath: str) -> Tuple[Dict[str, Dict[str, str]], List[Tuple[str, str]]]:
    nodes: Dict[str, Dict[str, str]] = {}
    edges: List[Tuple[str, str]] = []
    with open(filePath, 'r', encoding='utf-8') as file:
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

def createGraphFromDpd(filePath: str) -> nx.DiGraph:
    nodes, edges = parseDpdFile(filePath)
    G = nx.DiGraph()
    for nodeId, data in nodes.items():
        G.add_node(nodeId, **data)
    G.add_edges_from(edges)
    return G

def get_second_word(text: str) -> str:
    if not text:
        return ""
    tokens = text.split()
    if len(tokens) < 2:
        return ""
    return tokens[1].replace(":", "")

def main() -> None:
    coq_file = r'C:\Users\User\Documents\GitHub\autoformalization\src\dataset\single_file_data\lf\EverythingLF.v'
    dpd_file = r'C:\Users\User\Documents\GitHub\autoformalization\src\dependency_graph\EverythingLF.dpd'
    tmp_preprocessed_path = coq_file + ".tmp"
    formatCoqFile(coq_file, tmp_preprocessed_path)

    with open(tmp_preprocessed_path, "r", encoding="utf-8") as f:
        preprocessed_content = f.read()

    os.remove(tmp_preprocessed_path)
    items = extractBlocksFromPreprocessed(preprocessed_content)
    items = [itm for itm in items if itm["raw"].strip() != ""]
    data_records = []
    for itm in items:
        data_records.append({
            "Type": itm["type"],
            "Chunk": itm["raw"]
        })
    df = pd.DataFrame(data_records)
    G = createGraphFromDpd(dpd_file)
    df["Label"] = df["Chunk"].apply(get_second_word)
    graph_data = []
    for node, attributes in G.nodes(data=True):
        graph_data.append({
            "GraphNodeId": node,
            "GraphLabel": attributes.get("label", "")
        })
    df_graph = pd.DataFrame(graph_data)
    merged_df = df.merge(df_graph, left_on="Label", right_on="GraphLabel", how="left")

    def get_dependencies_labels(node_id: str) -> Optional[List[str]]:
        if pd.isna(node_id):
            return None
        successors = list(G.successors(node_id))
        if not successors:
            return None
        return [G.nodes[s]["label"] for s in successors]

    merged_df["Dependencies"] = merged_df["GraphNodeId"].apply(get_dependencies_labels)
    columns_to_drop = ["Label", "GraphNodeId", "GraphLabel"]
    merged_df.drop(columns=columns_to_drop, inplace=True)
    out_file = r'C:\Users\User\Documents\GitHub\autoformalization\src\dataset\processed_data\df.json'
    merged_df.to_json(out_file, orient="records", indent=2, force_ascii=False)
    print(f"Done. Final JSON saved to: {out_file}")

if __name__ == "__main__":
    main()
