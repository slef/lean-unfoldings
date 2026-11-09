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

[QuotientRetraction.lean](QuotientRetraction.lean) supplies continuous quotient
descent and contractibility of retracts. [PuncturedSphere.lean](PuncturedSphere.lean)
derives contractibility of a punctured unit sphere by stereographic projection.
The source application retracts the punctured surface onto its actual cut locus.

[GraphExtension.lean](GraphExtension.lean) extends compatible vertex and edge
maps continuously to the carrier. [ContractibleLift.lean](ContractibleLift.lean)
lifts maps from contractible spaces through surjective covering maps.
[GraphPotential.lean](GraphPotential.lean) uses the circle covering to construct
a real potential changing along one selected edge and constant along all other
edges. [GraphAcyclic.lean](GraphAcyclic.lean) proves that a contractible finite
embedded graph is simple and its adjacency graph is a tree. This proves the
source cut-locus tree theorem without Euler counting or planar separation.

[FiniteClasses.lean](FiniteClasses.lean) proves a generic finite-relation-class
lemma used to separate triangle seam classes. Rotation systems, spherical
cellulations, Euler's formula, and the tree/disk criteria remain open. A face
walk must not be treated as a proved complementary region of an embedding, and
Euler's formula must not be an axiom or a definition of spherical topology.
