import os
import json
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional

# Function to parse .dpd file
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

# Function to create a NetworkX graph
def createGraphFromDpd(filePath: str) -> nx.DiGraph:
    nodes, edges = parseDpdFile(filePath)
    G = nx.DiGraph()
    for nodeId, data in nodes.items():
        G.add_node(nodeId, **data)
    G.add_edges_from(edges)
    return G

# Function to extract the second word as a label
def get_second_word(text: str) -> str:
    if not text:
        return ""
    tokens = text.split()
    if len(tokens) >= 2:
        return tokens[1].replace(':', '')
    return ""

# Function to parse attributes safely
def parse_attributes(attr_str: str) -> dict:
    attr_str = attr_str.strip("[];")
    attr_pairs = attr_str.split(", ")
    attr_dict = {}
    for pair in attr_pairs:
        if "=" in pair:
            key, value = pair.split("=")
            attr_dict[key.strip()] = value.strip().strip('"')
    return attr_dict

def main():
    # 1) Paths
    BASE_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    dpdFilePath = r'C:\Users\User\Documents\GitHub\autoformalization\src\dependency_graph\EverythingLF.dpd'

    # Single-file dataset JSON from step (1)
    single_file_json_path = os.path.join(BASE_DIR, "dataset", "processed_data", "coq_proofs_dataset_single.json")

    # Where to store final merged result
    output_file = os.path.join(BASE_DIR, "dataset", "processed_data", "df_single.json")

    # 2) Build graph from .dpd file
    G = createGraphFromDpd(dpdFilePath)

    # 3) Load single-file dataset
    with open(single_file_json_path, "r", encoding='utf-8') as f:
        json_data = json.load(f)

    # Extract JSON data into DataFrame
    data_records = []
    for file_entry in json_data:
        file_name = file_entry.get("fileName", "")
        items = file_entry.get("items", [])
        for item in items:
            raw_text = item.get("raw", "")
            item_type = item.get("type", "")
            data_records.append({
                "fileName": file_name,
                "type": item_type,
                "raw": raw_text
            })

    df = pd.DataFrame(data_records)

    # 4) Extract "Label" column from `raw`
    df["Label"] = df["raw"].apply(get_second_word)

    # 5) Extract node attributes from G into a DataFrame
    expanded_data = []
    for node, attributes in G.nodes(data=True):
        expanded_data.append({"Node": node, "Label": attributes.get("label", "Unknown")})

    df_dpd = pd.DataFrame(expanded_data)

    # 6) Merge `df` and `df_dpd` on "Label"
    merged_df = df.merge(df_dpd, on="Label", how="left")

    # 7) Collect dependencies from each Node
    def get_dependencies_labels(node: str) -> Optional[List[str]]:
        if not node or node not in G.nodes:
            return None
        successors = list(G.successors(node))
        if not successors:
            return None
        return [G.nodes[s]["label"] for s in successors]

    merged_df["dependencies"] = merged_df["Node"].apply(get_dependencies_labels)

    # 8) Write final result to JSON
    merged_df.to_json(output_file, orient="records", indent=2)
    print(f"Merged dataset saved to {output_file}")

if __name__ == "__main__":
    main()
