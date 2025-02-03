import os
import re

dpd_dir = "/root/lf/dgraph"  # Directory where individual .dpd files are stored
output_file = os.path.join(dpd_dir, "dgraph.dpd")

node_map = {}  # Maps node_name → unique global ID and attributes
next_global_id = 1  # Counter for unique IDs
edges = []  # Stores final edges

def process_dpd_file(file_path):
    """ Read and process a .dpd file, preserving node attributes and updating IDs. """
    global next_global_id

    local_map = {}  # Old ID → New global ID for this file
    file_edges = []
    node_lines = []  # Store nodes with attributes

    with open(file_path, "r") as f:
        for line in f:
            node_match = re.match(r'N: (\d+) "(.*?)" (\[.*?\])?;', line)  # Extract nodes
            edge_match = re.match(r'E: (\d+) (\d+) (\[.*?\])?;', line)  # Extract edges

            if node_match:
                old_id, node_name, attributes = node_match.groups()
                old_id = int(old_id)
                attributes = attributes if attributes else ""  # Preserve attributes

                # Assign global ID if not seen before
                if node_name not in node_map:
                    node_map[node_name] = (next_global_id, attributes)
                    next_global_id += 1

                local_map[old_id] = node_map[node_name][0]

            elif edge_match:
                old_src, old_dst, edge_attr = edge_match.groups()
                old_src, old_dst = int(old_src), int(old_dst)
                edge_attr = edge_attr if edge_attr else ""  # Preserve edge attributes
                file_edges.append((old_src, old_dst, edge_attr))

    # Update edges using local-to-global mapping
    updated_edges = [(local_map[src], local_map[dst], attr) for src, dst, attr in file_edges]

    return updated_edges

# Process all `.dpd` files
all_files = [f for f in os.listdir(dpd_dir) if f.endswith(".dpd")]
final_edges = []

for file in all_files:
    file_path = os.path.join(dpd_dir, file)
    final_edges.extend(process_dpd_file(file_path))

# Write merged output
with open(output_file, "w") as f:
    for node_name, (global_id, attributes) in node_map.items():
        f.write(f"N: {global_id} \"{node_name}\" {attributes};\n")
    
    for src, dst, attr in final_edges:
        f.write(f"E: {src} {dst} {attr};\n")

print(f"Dependency graphs merged successfully into {output_file}")
