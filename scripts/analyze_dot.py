#!/usr/bin/env python3
"""Analyze DAG health from a .dot file."""
import argparse
from pathlib import Path

import networkx as nx
import pydot

DOT_FILE = Path("dag/dag.dot")
DEFAULT_ROOT = "thm:rh_from_real_simple_spectrum"


def load_dot_graph(dot_path: Path, verbose: bool = False) -> nx.DiGraph:
    try:
        graphs = pydot.graph_from_dot_file(str(dot_path))
        if not graphs:
            raise ValueError("No graphs found in DOT file.")

        G = nx.DiGraph()

        for edge in graphs[0].get_edges():
            src = edge.get_source().strip('"')
            dst = edge.get_destination().strip('"')
            G.add_edge(src, dst)
            if verbose:
                print(f"[edge] {src} → {dst}")

        for node in graphs[0].get_nodes():
            name = node.get_name().strip('"')
            if name.lower() in {"node", "graph", "edge"} or name.startswith("node"):
                continue
            if name and name not in G:
                G.add_node(name)
                if verbose:
                    print(f"[node] {name}")

        return G
    except Exception as e:
        raise RuntimeError(f"Error loading DOT file: {e}")


def name_component(nodes: set[str]) -> str:
    if "thm:det_identity_revised" in nodes:
        return "RH Core"
    if "thm:spectral_determinant_identity_Lpi" in nodes:
        return "GRH Generalization"
    if "lem:heat_trace_expansion" in nodes:
        return "Heat Trace Analytics"
    if "lem:spectral_encoding_injection" in nodes:
        return "Forward Implication Chain"
    if "lem:trace_distribution_positivity" in nodes:
        return "Trace Positivity"
    if "lem:spectral_symmetry" in nodes:
        return "Symmetry Properties"
    if "cor:spectral_determines_zeta" in nodes:
        return "Zeta Encoding"
    return "Unclassified"


def analyze_graph(G: nx.DiGraph, root: str, show_components: bool = False):
    print("📊 DAG Health Analysis")

    orphan_nodes = sorted([
        n for n in G.nodes
        if G.degree(n) == 0 and n.lower() != "node"
    ])
    root_nodes = sorted([n for n in G.nodes if G.in_degree(n) == 0])
    leaf_nodes = sorted([n for n in G.nodes if G.out_degree(n) == 0])

    components = list(nx.weakly_connected_components(G))
    largest_component = max(components, key=len)
    disconnected_nodes = sorted([
        n for n in G.nodes if n not in largest_component and n.lower() != "node"
    ])

    try:
        depths = nx.single_source_shortest_path_length(G.reverse(), root)
        max_depth = max(depths.values())
    except Exception:
        depths = {}
        max_depth = None

    print(f"Total Nodes               : {G.number_of_nodes()}")
    print(f"Total Edges               : {G.number_of_edges()}")
    print(f"Orphan Nodes              : {len(orphan_nodes)}")
    print(f"Root Nodes                : {len(root_nodes)}")
    print(f"Leaf Nodes                : {len(leaf_nodes)}")
    print(f"Disconnected Nodes        : {len(disconnected_nodes)}")
    print(f"Critical Path Depth       : {max_depth}")

    if orphan_nodes:
        print("\n🚫 Orphan Nodes (no edges):")
        for n in orphan_nodes:
            print(f"  - {n}")

    if disconnected_nodes:
        print("\n🔌 Disconnected Nodes (not in main component):")
        for n in disconnected_nodes:
            print(f"  - {n}")

    if max_depth is None:
        print(f"\n⚠️ Could not compute critical path from root node: {root}")

    if show_components:
        print("\n🔗 Connected Components:")
        for i, comp in enumerate(sorted(components, key=len, reverse=True), 1):
            label = name_component(comp)
            print(f"  Component {i} — {label} (size={len(comp)}):")
            for node in sorted(comp):
                print(f"    - {node}")


def main():
    parser = argparse.ArgumentParser(description="Analyze DAG health from a .dot file.")
    parser.add_argument("--dot", type=str, default=str(DOT_FILE), help="Path to .dot file")
    parser.add_argument("--depth-node", type=str, default=DEFAULT_ROOT, help="Root node to measure depth from")
    parser.add_argument("--verbose", action="store_true", help="Verbose: show all parsed edges/nodes")
    parser.add_argument("--components", action="store_true", help="Print all connected components and their nodes")

    args = parser.parse_args()
    G = load_dot_graph(Path(args.dot), verbose=args.verbose)
    analyze_graph(G, root=args.depth_node, show_components=args.components)


if __name__ == "__main__":
    main()
