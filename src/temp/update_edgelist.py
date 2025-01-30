import re

def update_edgelist_ids(input_file, output_file):
    with open(input_file, 'r') as f:
        lines = f.readlines()

    nodes = {}
    edges = []

    node_pattern = re.compile(r'N: (\d+) "([^"]+)"')
    edge_pattern = re.compile(r'E: (\d+) (\d+) \[weight=\d+,\s*\]')

    current_node_id = 1

    for line in lines:
        match = node_pattern.match(line)
        if match:
            old_id = match.group(1)
            name = match.group(2)
            nodes[name] = current_node_id
            current_node_id += 1

    for line in lines:
        match = edge_pattern.match(line)
        if match:
            node1_id = match.group(1)
            node2_id = match.group(2)
            node1_name = [name for name, id in nodes.items() if id == int(node1_id)][0]
            node2_name = [name for name, id in nodes.items() if id == int(node2_id)][0]
            new_node1_id = nodes[node1_name]
            new_node2_id = nodes[node2_name]
            edges.append(f'E: {new_node1_id} {new_node2_id} [weight=1, ]\n')

    with open(output_file, 'w') as f:
        for name, new_id in nodes.items():
            f.write(f'N: {new_id} "{name}" [body=yes, kind=cnst, prop=yes, path="Maps", ];\n')

        for edge in edges:
            f.write(edge)

input_filepath = 'src\dataset\dependancy_graph\dgraph.dpd'
output_filepath = 'src\temp\dgraph_updated.dpd'

update_edgelist_ids(input_filepath, output_filepath)
