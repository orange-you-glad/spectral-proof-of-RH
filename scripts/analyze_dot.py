#!/usr/bin/env python3
"""Analyze DAG health from a .dot file."""
from pathlib import Path

import networkx as nx
import pydot

DOT_FILE = Path("dag/dag.dot")
ROOT_NODE = "thm:rh_from_real_simple_spectrum"

def load_dot_graph(dot_path):
    try:
        graphs = pydot.graph_from_dot_file(str(dot_path))
        if not graphs:
            raise ValueError("No graphs found in DOT file.")
        G = nx.DiGraph()
        for edge in graphs[0].get_edges():
            src = edge.get_source().strip('"')
            dst = edge.get_destination().strip('"')
            G.add_edge(src, dst)
        for node in graphs[0].get_nodes():
            name = node.get_name().strip('"')
            if name and name not in G:
                G.add_node(name)
        return G
    except Exception as e:
        raise RuntimeError(f"Error loading DOT file: {e}")


def analyze_graph(G):
    print("📊 DAG Health Analysis")

    orphan_nodes = sorted([n for n in G.nodes if G.degree(n) == 0])
    root_nodes = sorted([n for n in G.nodes if G.in_degree(n) == 0])
    leaf_nodes = sorted([n for n in G.nodes if G.out_degree(n) == 0])

    # Connected components (weakly)
    components = list(nx.weakly_connected_components(G))
    largest_component = max(components, key=len)
    disconnected_nodes = sorted([n for n in G.nodes if n not in largest_component])

    # Critical path from main RH theorem
    try:
        depths = nx.single_source_shortest_path_length(G.reverse(), ROOT_NODE)
        max_depth = max(depths.values())
    except Exception:
        depths = {}
        max_depth = None

    # Print Summary
    print(f"Total Nodes               : {G.number_of_nodes()}")
    print(f"Total Edges               : {G.number_of_edges()}")
    print(f"Orphan Nodes              : {len(orphan_nodes)}")
    print(f"Root Nodes                : {len(root_nodes)}")
    print(f"Leaf Nodes                : {len(leaf_nodes)}")
    print(f"Disconnected Nodes        : {len(disconnected_nodes)}")
    print(f"Critical Path Depth       : {max_depth}")

    # Show problematic nodes if any
    if orphan_nodes:
        print("\n🚫 Orphan Nodes (no edges):")
        for n in orphan_nodes:
            print(f"  - {n}")

    if disconnected_nodes:
        print("\n🔌 Disconnected Nodes (not in main component):")
        for n in disconnected_nodes:
            print(f"  - {n}")

    if not max_depth:
        print(f"\n⚠️ Could not compute critical path from {ROOT_NODE}")

def main():
    G = load_dot_graph(DOT_FILE)
    analyze_graph(G)

if __name__ == "__main__":
    main()
