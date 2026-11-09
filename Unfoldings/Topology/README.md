# Embedded graphs and surface cellulations

This subtree contains topology developed independently of
polyhedral metrics and proposed for Mathlib. Its definitions and proofs should
not import `Unfoldings.Metric`, `Unfoldings.Geometry`, or developments.

The [feature checklist](../../PLAN.md#embedded-graphs-and-surface-cellulations)
includes rotation systems, actual embeddings, Euler's formula, primal/dual tree
duality, and tree complements on spheres and disks. Loops and parallel edges
must be supported where quotienting a boundary produces them.

[FiniteEmbeddedGraph.lean](FiniteEmbeddedGraph.lean) records actual vertex and
continuous edge maps, including loops and parallel edges, and exports a Mathlib
multigraph. Open edges avoid vertices and each other. Compactness and
topological connectedness of the carrier give graph connectedness. Forgetting
loops and multiplicity is used only for reachability, not to assert acyclicity.

[FiniteSubdivision.lean](FiniteSubdivision.lean) proves existence and uniqueness
of consecutive marked intervals. Geometry modules use this to subdivide finite
straight networks; the graph interface itself has no geometry dependency.

[FiniteClasses.lean](FiniteClasses.lean) proves a generic finite-relation-class
lemma used to separate triangle seam classes. Rotation systems, spherical
cellulations, Euler's formula, and the tree/disk criteria remain open. A face
walk must not be treated as a proved complementary region of an embedding, and
Euler's formula must not be an axiom or a definition of spherical topology.
