import os
import re
import pandas as pd
import json
import networkx as nx
from typing import Dict, List, Tuple, Optional

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
    if len(tokens) >= 2:
        return tokens[1].replace(':', '')
    return ""

def parse_attributes(attr_str: str) -> dict:
    attr_str = attr_str.strip("[];")
    attr_pairs = attr_str.split(", ")
    attr_dict = {}
    for pair in attr_pairs:
        if "=" in pair:
            key, value = pair.split("=")
            attr_dict[key.strip()] = value.strip().strip('"')
    return attr_dict

def extract_filename(path: str) -> str:
    if not path:
        return ""
    return path.split(".")[0] + ".v"

def main():
    # Adjust BASE_DIR to be the parent of the current directory (i.e., src)
    BASE_DIR: str = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    
    # Build the paths relative to BASE_DIR
    dpdDir: str = os.path.join(BASE_DIR, "dataset", "dependency_graph")
    dpdFilePath: str = os.path.join(dpdDir, "dgraph.dpd")
    
    if not os.path.exists(dpdDir):
        print(f"Warning: Directory '{dpdDir}' does not exist. Creating it now.")
        os.makedirs(dpdDir, exist_ok=True)
        print(f"Created missing directory: {dpdDir}")

    # Directory for processed data output and Coq proofs dataset
    processedDataDir: str = os.path.join(BASE_DIR, "dataset", "processed_data")
    if not os.path.exists(processedDataDir):
        print(f"Warning: Directory '{processedDataDir}' does not exist. Creating it now.")
        os.makedirs(processedDataDir, exist_ok=True)
        print(f"Created missing directory: {processedDataDir}")

    coqDatasetPath: str = os.path.join(BASE_DIR, "dataset", "processed_data", "coq_proofs_dataset.json")
    output_file: str = os.path.join(processedDataDir, "df.json")

    # Create graph from the dependency graph file
    G = createGraphFromDpd(dpdFilePath)

    # Load the Coq proofs dataset
    with open(coqDatasetPath, "r", encoding='utf-8') as file:
        json_data = json.load(file)

    # Build DataFrame from the Coq dataset
    data = []
    for entry in json_data:
        file_name = entry.get("fileName", "")
        items = entry.get("items", [])
        for item in items:
            raw_text = item.get("raw", "")
            item_type = item.get("type", "")
            data.append({"fileName": file_name, "type": item_type, "raw": raw_text})

    df = pd.DataFrame(data)
    df["Label"] = df["raw"].apply(get_second_word)

    # Process nodes from the dependency graph
    expanded_data = []
    for node, attributes in G.nodes(data=True):
        attrs = parse_attributes(attributes["attributes"])
        expanded_data.append({"Node": node, "Label": attributes["label"], **attrs})

    df_dpd = pd.DataFrame(expanded_data)
    
    # If your 'dpd' nodes have a 'path' attribute, extract the .v filename from it
    if "path" in df_dpd.columns:
        df_dpd["file"] = df_dpd["path"].apply(extract_filename)
    else:
        df_dpd["file"] = ""

    # Merge Coq DataFrame with the DPD DataFrame
    merged_df = df.merge(
        df_dpd[["file", "Label", "Node"]],
        left_on=["fileName", "Label"],
        right_on=["file", "Label"],
        how="left"
    )

    merged_df.drop(columns=["file"], inplace=True)
    merged_df["Node"] = merged_df["Node"].fillna(pd.NA)

    df_merged = merged_df.dropna(subset=["Node"])
    if "level" in df_merged.columns:
        df_merged = df_merged.sort_values(by=["level", "fileName"])
    else:
        df_merged = df_merged.sort_values(by=["fileName"])

    def get_dependencies_labels(node: str) -> Optional[List[str]]:
        """
        Return a list of labels corresponding to:
        - the labels of any outgoing nodes (dependencies)
        If there are no outgoing nodes, return None (which will become `null` in JSON).
        """
        if node not in G.nodes:
            return None

        successors = list(G.successors(node))  # Get outgoing edges
        if not successors:
            return None  # Return None when no dependencies exist

        # Get labels of all dependent nodes
        return [G.nodes[s]["label"] for s in successors]


    # Create a 'dependencies' column
    df_merged["dependencies"] = df_merged["Node"].apply(get_dependencies_labels)

    # Write the merged DataFrame to JSON
    df_merged.to_json(output_file, orient="records", indent=2)
    print(f"Data successfully stored in JSON format at: {output_file}")

if __name__ == "__main__":
    main()
