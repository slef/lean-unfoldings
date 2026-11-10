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

[BoundaryQuotient.lean](BoundaryQuotient.lean) treats quotient maps whose
nontrivial fibers lie on a distinguished boundary. It proves boundary-complement
homeomorphisms and descent of punctured boundary retractions.
[BallBoundaryQuotient.lean](BallBoundaryQuotient.lean) constructs the retraction
for a closed ball and identifies the complement of its boundary image with an
open ball. A spherical target forces a finite embedded boundary graph to be a
tree. The triangle seam-restoration and source-disk constructions both use this
API. The convex-sphere primal cut-tree converse is now constructed in the
[application layer](../Polyhedron/CutDiskConverse.lean).

[CircleObstruction.lean](CircleObstruction.lean) and [DiskDegree.lean](DiskDegree.lean)
prove the circle obstruction and the interior coverage of boundary-fixing disk
maps. [PlanarOpenMapping.lean](PlanarOpenMapping.lean) derives planar invariance
of domain using the pinned, licensed Jordan–Schönflies library. The actual bank
boundary is now proved to be preserved by every disk homeomorphism of a
spatially folded triangle complex, including at its vertices.

[FiniteClasses.lean](FiniteClasses.lean) proves a generic finite-relation-class
lemma used to separate triangle seam classes. Rotation systems, spherical
cellulations, and Euler's formula remain open. A face walk must not be treated as a proved complementary region of an embedding, and
Euler's formula must not be an axiom or a definition of spherical topology.

[RootedForest.lean](RootedForest.lean) proves that adjoining one outside vertex
joined to every marked root gives a tree exactly for a forest with one root per
component. It also constructs the root/component bijection. Empty vertex types
are allowed; examples check both missing roots and multiple roots in a component.
[GraphRootExtension.lean](GraphRootExtension.lean) proves the corresponding
multigraph equivalence, preserving loops and parallel edges.
[GraphRootQuotient.lean](GraphRootQuotient.lean) recovers rooted forests from
tree quotients identifying exactly the roots. The actual disk-cut bridge is
proved in [RelativeCutForest.lean](../Complex/RelativeCutForest.lean).

[BoundaryCollapse.lean](BoundaryCollapse.lean) collapses a closed boundary to
infinity in its complement. [DiskSphereQuotient.lean](DiskSphereQuotient.lean)
constructs the disk-boundary-to-sphere quotient using Mathlib's one-point sphere
homeomorphism. [DiskSubsetChart.lean](DiskSubsetChart.lean) gives the open planar
model for disk complements avoiding the original boundary.

[Quadrant.lean](Quadrant.lean) gives a piecewise linear homeomorphism from a
closed quadrant to a closed half-plane, preserving the apex and identifying
the two rays with the boundary line. Actual interval-link tangent fans use
this in the geometry layer; total angle and overlap impose no topological
restriction on their half-plane models.

[BoundaryPush.lean](BoundaryPush.lean), [HalfPlanePush.lean](HalfPlanePush.lean),
[SmallHalfPlanePush.lean](SmallHalfPlanePush.lean), and [LocalPush.lean](LocalPush.lean)
construct and combine local inward pushes. [BoundaryAtlas.lean](BoundaryAtlas.lean)
proves that a compact Hausdorff space with actual half-plane boundary charts
embeds into its boundary complement. Composing with a boundary quotient gives
an embedding into the target off the boundary image. The triangle application
constructs these charts for the actual cut banks, including all vertex copies.
This separates the banks and supplies the embedding used by the cut-tree
disk construction.

[PlanarHalfPlane.lean](PlanarHalfPlane.lean) transfers planar openness to product
coordinates and rules out planar injections hitting the half-plane boundary.
[BallExtension.lean](BallExtension.lean) radially extends sphere homeomorphisms
to closed balls with exact boundary agreement and preserved radius.

[GraphEmbedding.lean](GraphEmbedding.lean) transports actual graph carriers
through continuous injections. [GraphVertexMap.lean](GraphVertexMap.lean) and
[GraphFinitePath.lean](GraphFinitePath.lean) preserve or construct multigraph
walks, paths, and cycles. [GraphDrawing.lean](GraphDrawing.lean) bridges the
actual edge parametrizations to the pinned cycle-to-Jordan theorem.
[GraphForestMap.lean](GraphForestMap.lean) proves that a cycle mapped to a
forest must repeat the image of its distinguished edge on the alternate path.
[SphereChart.lean](SphereChart.lean) supplies Euclidean homeomorphisms from
punctured spheres. The triangle application now constructs whole-cut planar
embeddings and Jordan cycles through every bank. A connected primal cut forest
now gives one boundary cycle covering every bank end.

[CompactJordanDisk.lean](CompactJordanDisk.lean) proves that a compact planar set
with nonempty interior and Jordan frontier is a disk. [BoundaryInvariance.lean](BoundaryInvariance.lean)
identifies that frontier from actual half-plane charts and an open planar model
of the boundary complement. [DiskFromBoundary.lean](DiskFromBoundary.lean)
combines these constructions. [SphereSubsetChart.lean](SphereSubsetChart.lean)
supplies the open Euclidean model for closed-set complements in a sphere.
The convex-sphere application now constructs the actual disk homeomorphism
from a connected acyclic primal cut multigraph, with exact bank boundary.
