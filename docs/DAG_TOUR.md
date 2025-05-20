# DAG Tour

The proof is organized as a Directed Acyclic Graph (DAG) of formal results.
Each node corresponds to a lemma, theorem, or definition. Edges encode logical
or spectral dependencies. Maintaining this structure ensures that the spectral
realization of the Riemann Hypothesis remains reproducible and auditable.

## Why a DAG?

The spectral approach introduces many intermediate results. The DAG records the
exact dependency chain so contributors can safely refine statements without
introducing cycles.

## Chapter Mapping

Each chapter directory under `src/chapters/` maps onto one or more DAG nodes.
Nodes reference their source files via labels and are listed in `dag/dag_nodes.json`.

## Adding Edges

1. Declare the new edge in `dag/dag_edges.json`.
2. Update `dag/dag_nodes.json` if new nodes are introduced.
3. Re-run `python3 scripts/dag_visualizer.py` to refresh the visualization.

Always run `make check` to verify that the DAG remains acyclic and all nodes are
accounted for.

## Usage

Run `python dag/dag_audit.py --check` to verify the graph, and view `dag/dag.dot` for a visualization.
