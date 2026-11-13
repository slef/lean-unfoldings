# Unfoldings

A Lean/Mathlib library for polyhedral metrics, cuts, and planar unfoldings.
The main result constructs a finite nonoverlapping **source unfolding of a convex
polyhedron at every nonextreme source point**. General developments can overlap;
nonoverlap is a separate property.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The repository pins Lean and Mathlib **4.35.0**. The build checks the library,
examples, and a proof-dependency audit allowing only standard Lean axioms.
See the [build reference](docs/REFERENCE.md#build-and-proof-audit) for cache options
and audit details.

## Use the source-unfolding theorem

Start with [Source/Unfolding.lean](Unfoldings/Source/Unfolding.lean).
Its input is a triangulated surface with a spatial folding `F` and a proof
`P : F.ConvexBoundary` that the surface is the boundary of a full-dimensional
convex hull. Given a nonextreme source, construct the unfolding as follows:

```lean
import Unfoldings.Source.Unfolding

open Unfoldings

noncomputable section

example {Face : Type} [Fintype Face] {C : TriangleComplex Face}
    {F : SpatialFolding C} (P : F.ConvexBoundary)
    (source : C.Realization Set.univ)
    (hsource : F.toSpace Set.univ source ∉ F.vertexHull.extremePoints ℝ) :
    letI := P.metricSpace
    SourceUnfolding (C := C) source := by
  letI := P.metricSpace
  exact P.sourceUnfoldingOfNonextreme source hsource
```

The resulting `U : SourceUnfolding source` provides:

- `U.layout` and `U.nonoverlapping`: finitely many convex polygon pieces with
  disjoint interiors and rigid maps into original triangles.
- `U.disk` and `U.intrinsic_distance`: a completed cut surface homeomorphic to
  a closed disk, with the cut metric identified with intrinsic path distance.
- `U.boundary_projection`: the net boundary projects exactly onto the cut locus.
- `U.radial_shortest_path` and `U.source_distance_preserved`: radial lifts of
  every shortest path, including distinct boundary copies at tied endpoints.

`P.sourceUnfolding source regular` is an alternative constructor when you
already have an intrinsic regularity proof. Sources on creases and flat
subdivision vertices are included. These noncomputable constructions expose
data and theorems for use in further proofs.

For an independent formal statement, read [Source/Abstract.lean](Unfoldings/Source/Abstract.lean).
Its general `IsNetOf` predicate describes a disk that folds rigidly onto a spatial
surface. The source theorem constructs a valid net of the given polyhedron with
the additional shortest-path properties. Construction proofs live in
[Source/AbstractBridge.lean](Unfoldings/Source/AbstractBridge.lean).
Import `Unfoldings.Source.Abstract`; `lake build` checks both the proof and the
independence of its public definitions and statements.

## Find your starting point

| Goal | Start here |
| --- | --- |
| Read the main result and its output API | [Source/Unfolding.lean](Unfoldings/Source/Unfolding.lean) |
| Read an independent statement of source unfolding | [Source/Abstract.lean](Unfoldings/Source/Abstract.lean) |
| Define a triangulated surface and its cuts | [Complex.lean](Unfoldings/Complex.lean) |
| Supply an embedded convex-boundary model | [Complex/Folding.lean](Unfoldings/Complex/Folding.lean), [Polyhedron/Convex.lean](Unfoldings/Polyhedron/Convex.lean) |
| Work with overlapping or nonoverlapping layouts | [Development.lean](Unfoldings/Development.lean), [PolygonalLayout.lean](Unfoldings/PolygonalLayout.lean) |
| Understand the metric construction | [Metric/Route.lean](Unfoldings/Metric/Route.lean), [Metric/Gluing.lean](Unfoldings/Metric/Gluing.lean) |
| Characterize disk cuts of a convex sphere | [Polyhedron/CutDiskIff.lean](Unfoldings/Polyhedron/CutDiskIff.lean) |
| Cut a disk along a rooted forest | [Complex/RelativeCutForest.lean](Unfoldings/Complex/RelativeCutForest.lean) |
| Instantiate a complete convex polyhedron | [Examples/Tetrahedron.lean](Unfoldings/Examples/Tetrahedron.lean) |
| Develop a flat metric disk, with overlap allowed | [Development/FlatDisk.lean](Unfoldings/Development/FlatDisk.lean) |
| Cut polygonal forests carried by a refinement | [Complex/PolygonalCuts.lean](Unfoldings/Complex/PolygonalCuts.lean), [Complex/PolygonalCutGraph.lean](Unfoldings/Complex/PolygonalCutGraph.lean) |
| Refine triangles without changing intrinsic geometry | [Complex/SubdivisionMetric.lean](Unfoldings/Complex/SubdivisionMetric.lean), [Examples/Subdivision.lean](Unfoldings/Examples/Subdivision.lean) |
| Unfold a sufficiently flat acute convex cap to a simple polygon | [Cap/SimpleEdgeUnfolding.lean](Unfoldings/Cap/SimpleEdgeUnfolding.lean) |
| Unfold an acute convex roof with arbitrary boundary heights | [Roof/SimpleEdgeUnfolding.lean](Unfoldings/Roof/SimpleEdgeUnfolding.lean) |
| Inspect a concrete nonflat convex cap | [Examples/Pyramid.lean](Unfoldings/Examples/Pyramid.lean) |
| Try small examples | [Examples/Metric.lean](Unfoldings/Examples/Metric.lean), [Examples/Hinge.lean](Unfoldings/Examples/Hinge.lean) |

For a specific lemma, use the [module index](docs/REFERENCE.md#module-index).
For development priorities, use the [feature checklist](PLAN.md); the
[session log](LOG.md) records how the proofs were built.

## Scope and next steps

The regular-source theorem and the finite embedded tree structure of its cut
locus are proved; see [Source/CutTree.lean](Unfoldings/Source/CutTree.lean).
The [sphere criterion](Unfoldings/Polyhedron/CutDiskIff.lean) proves that the
canonical primal cut multigraph is a tree exactly when the cut is a disk.
The [disk criterion](Unfoldings/Complex/RelativeCutForest.lean) proves the
corresponding rooted-forest equivalence, including empty cuts. Both construct
actual disk homeomorphisms and allow overlapping developments.
Conforming refinements preserve intrinsic distances, spatial foldings,
developments, and nonoverlap. A triangulated disk with a spatial folding and
total angle `2π` at every interior vertex has a locally isometric development,
unique after fixing one face.
Polygonal cuts use supplied conforming refinement certificates.

[O'Rourke's nearly flat cap theorem](Unfoldings/Cap/SimpleEdgeUnfolding.lean) is
also proved. A positive acute margin determines a tilt threshold uniform over
all input meshes. The result constructs original-edge forest cuts, an intrinsic
cut disk, and a globally injective development with a simple polygon boundary.
See the [cap theorem guide](docs/CAP_THEOREM.md) for its output API and proof.

For an independent statement, read [Cap/Abstract.lean](Unfoldings/Cap/Abstract.lean).
Its definitions and theorem state the mathematical claim; Lean checks the proof
through [AbstractBridge.lean](Unfoldings/Cap/AbstractBridge.lean). Import
`Unfoldings.Cap.Abstract`; the usual `lake build` checks it and audits that its
public definitions and statements use only the abstract suite and Mathlib.

The [arbitrary-rim acute-roof theorem](Unfoldings/Roof/SimpleEdgeUnfolding.lean)
extends this conclusion to roofs over convex polygons with unrestricted boundary
heights. Its positive tilt threshold also depends only on the acute margin.
See the [roof guide](docs/ROOFS.md) for inputs, outputs, and the proof structure.

Remaining work includes:

- Sources at genuine cone vertices, which need sector-valued source frames.
- Automatic refinement construction for supplied polygonal arcs.
- Star unfolding and the downstream tools needed for the Fewest Nets paper.

The [graph and cellulation layer](Unfoldings/Topology/README.md) is intended for
eventual Mathlib upstreaming. The current source-unfolding theorem does not
require a planar-graph Euler formula or a Jordan curve theorem.

Proof adaptations and prior-library credits are recorded in the
[provenance notes](docs/REFERENCE.md#provenance).
