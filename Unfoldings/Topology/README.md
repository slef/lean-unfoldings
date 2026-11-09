# Embedded graphs and surface cellulations

This subtree is reserved for topology that can be developed independently of
polyhedral metrics and proposed for Mathlib. Its definitions and proofs should
not import `Unfoldings.Metric`, `Unfoldings.Geometry`, or developments.

The [feature checklist](../../PLAN.md#embedded-graphs-and-surface-cellulations)
includes rotation systems, actual embeddings, Euler's formula, primal/dual tree
duality, and tree complements on spheres and disks. Loops and parallel edges
must be supported where quotienting a boundary produces them.

`FiniteClasses.lean` proves a generic finite-relation-class lemma, used to
separate triangle seam classes. No planar-graph or Euler theorem is implemented
here yet. A combinatorial face
walk must not be silently treated as a proved complementary region of an
embedding, and Euler's formula must not be an axiom or a definition of spherical
topology.
