#!/usr/bin/env python3
"""Validate DAG integrity if dag/ directory exists."""
import json
import os
import sys
from typing import Dict, Set, List

ROOT = "dag"


def load_json(path: str):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def check_coherence(nodes: Dict[str, dict], edges: Dict[str, List[str]]) -> list[str]:
    errors = []
    node_set: Set[str] = set(nodes)
    for src, dst_list in edges.items():
        if src not in node_set:
            errors.append(f"unknown source node: {src}")
        for dst in dst_list:
            if dst not in node_set:
                errors.append(f"edge {src}->{dst} references unknown node")
    # simple cycle check using DFS
    visiting: Set[str] = set()
    visited: Set[str] = set()

    def dfs(node: str) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        for nxt in edges.get(node, []):
            if dfs(nxt):
                return True
        visiting.remove(node)
        visited.add(node)
        return False

    for n in node_set:
        if dfs(n):
            errors.append("cycle detected in DAG")
            break
    return errors


def main() -> None:
    if not os.path.isdir(ROOT):
        print("❌ dag/ directory missing")
        sys.exit(1)
    nodes_path = os.path.join(ROOT, "dag_nodes.json")
    edges_path = os.path.join(ROOT, "dag_edges.json")
    if not os.path.isfile(nodes_path) or not os.path.isfile(edges_path):
        print("❌ DAG data files missing")
        sys.exit(1)
    nodes = load_json(nodes_path)
    edges = load_json(edges_path)
    errors = check_coherence(nodes, edges)
    if errors:
        for e in errors:
            print(f"❌ {e}")
        sys.exit(1)
    print("✅ DAG structure valid.")


if __name__ == "__main__":
    main()
