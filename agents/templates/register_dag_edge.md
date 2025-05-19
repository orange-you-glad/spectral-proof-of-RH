# Template: Register a DAG Edge

1. Open `dag/dag_edges.json`.
2. Add a new entry mapping the source node to its dependencies.
3. Ensure both source and destination nodes exist in `dag_nodes.json`.
4. Run `python3 scripts/dag_visualizer.py` to regenerate `dag/dag.dot`.
