import Mathlib

/-!
# Abstract graph-based scaffold for bounded unfolding thickness

This file is intentionally lightweight. It defines the main objects and theorem
statements for a future formalization of bounded unfolding thickness of convex
polyhedral metrics.

The hard geometry is represented by predicates for now. The goal is to obtain
stable, readable statements with `sorry`s, then refine the definitions later.
-/

noncomputable section

namespace Unfoldings

universe u

/-- The Euclidean plane. -/
abbrev Point2 : Type := EuclideanSpace ℝ (Fin 2)

/--
A finite triangulated polyhedral surface.

This is not merely a graph: faces are explicit data. The intended
interpretation is that each face is a Euclidean triangle with specified edge
lengths.
-/
structure TriangulatedSurface where
  V : Type u
  E : Type u
  F : Type u
  [fintypeV : Fintype V]
  [fintypeE : Fintype E]
  [fintypeF : Fintype F]
  /-- The two endpoints of an edge. This first scaffold uses ordered pairs. -/
  edgeVerts : E → V × V

  /-- The three vertices of each triangular face. -/
  faceVerts : F → Fin 3 → V

  /-- The three edges of each triangular face. -/
  faceEdges : F → Fin 3 → E

  /-- Edge lengths in the polyhedral metric. -/
  edgeLength : E → ℝ

  /-- Gaussian curvature at each vertex. -/
  curvature : V → ℝ

  /--
  Placeholder for the incidence axioms saying that this is a closed
  triangulated surface.
  -/
  isClosedTriangulatedSurface : Prop

attribute [instance] TriangulatedSurface.fintypeV
attribute [instance] TriangulatedSurface.fintypeE
attribute [instance] TriangulatedSurface.fintypeF

namespace TriangulatedSurface

/-- A cone point is a vertex with nonzero Gaussian curvature. -/
def IsConePoint (S : TriangulatedSurface.{u}) (v : S.V) : Prop :=
  S.curvature v ≠ 0

/-- A convex polyhedral metric is one with nonnegative curvature everywhere. -/
def IsConvexMetric (S : TriangulatedSurface.{u}) : Prop :=
  ∀ v : S.V, 0 ≤ S.curvature v

/-- Placeholder: the surface has sphere topology. -/
def IsSphere (_S : TriangulatedSurface.{u}) : Prop :=
  True

/-- Placeholder: the surface is a disphenoid metric. -/
def IsDisphenoidMetric (_S : TriangulatedSurface.{u}) : Prop :=
  True

/-- Placeholder: the surface is an edge-to-edge gluing of congruent squares. -/
def IsSquareGluingMetric (_S : TriangulatedSurface.{u}) : Prop :=
  True

/--
Placeholder: the surface is an edge-to-edge gluing of congruent equilateral
triangles.
-/
def IsEquilateralTriangleGluingMetric (_S : TriangulatedSurface.{u}) : Prop :=
  True

end TriangulatedSurface

/--
A refinement of a triangulated surface.

The refined surface may have new vertices and edges, but it represents the same
polyhedral metric. Old vertices preserve curvature, and new vertices are flat.
-/
structure SurfaceRefinement (S : TriangulatedSurface.{u}) where
  R : TriangulatedSurface.{u}

  /-- Old vertices as vertices of the refined surface. -/
  vertexMap : S.V → R.V

  /-- Placeholder: refined faces subdivide the old faces. -/
  subdividesFaces : Prop

  /-- Placeholder: the refinement preserves the metric. -/
  preservesMetric : Prop

  /-- Old vertices keep their curvature. -/
  curvature_old_vertices :
    ∀ v : S.V, R.curvature (vertexMap v) = S.curvature v

  /-- New vertices are flat, so refinement introduces no new cone points. -/
  new_vertices_flat :
    ∀ v : R.V, (∀ u : S.V, vertexMap u ≠ v) → R.curvature v = 0

/--
A cut tree in a refinement.

The cut is represented by a finite support set of vertices and a finite set of
refined edges. It is intended to be a tree spanning all cone points.
-/
structure CutTree (S : TriangulatedSurface.{u}) where
  refinement : SurfaceRefinement S

  /-- Vertices used by the cut tree. -/
  support : Finset refinement.R.V

  /-- Edges used by the cut tree. -/
  cutEdges : Finset refinement.R.E

  /-- Placeholder: endpoints of every cut edge lie in the support. -/
  edge_endpoints_in_support : Prop

  /--
  Placeholder: the cut graph is a tree on `support`.

  Later this can be replaced by a concrete `SimpleGraph.IsTree` statement.
  -/
  is_tree_on_support : Prop

  /-- The cut tree contains every cone point of the refined surface. -/
  spans_cone_points :
    ∀ v : refinement.R.V, refinement.R.IsConePoint v → v ∈ support

/--
A general unfolding obtained by cutting along a cut tree and placing triangular
pieces in the Euclidean plane.

The placement is part of the data. We do not need a uniqueness theorem for the
planar embedding at this stage.
-/
structure Unfolding (S : TriangulatedSurface.{u}) where
  cut : CutTree S

  Piece : Type u
  [fintypePiece : Fintype Piece]
  /-- Each planar piece comes from a face of the refined surface. -/
  sourceFace : Piece → cut.refinement.R.F

  /-- Planar positions of the three vertices of the triangular piece. -/
  placeVertex : Piece → Fin 3 → Point2

  /-- Placeholder: each placed triangle realizes the correct edge lengths. -/
  preserves_edge_lengths : Prop

  /-- Placeholder: adjacent uncut pieces are placed compatibly. -/
  compatible_on_uncut_edges : Prop

attribute [instance] Unfolding.fintypePiece

/--
Placeholder predicate: the relative interior of the placed triangular face `p`
contains the planar point `x`.

Later this should be replaced by a concrete definition using convex hulls or
barycentric coordinates.
-/
def faceInteriorContains
    {S : TriangulatedSurface.{u}} (_U : Unfolding S) (_p : _U.Piece)
    (_x : Point2) : Prop :=
  True

/-- The number of unfolded face interiors containing `x`. -/
def multiplicityAt
    {S : TriangulatedSurface.{u}} (U : Unfolding S) (x : Point2) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : U.Piece => faceInteriorContains U p x).card

/-- The unfolding has thickness at least `k`. -/
def ThicknessAtLeast
    {S : TriangulatedSurface.{u}} (U : Unfolding S) (k : ℕ) : Prop :=
  ∃ x : Point2, k ≤ multiplicityAt U x

/--
The surface has bounded unfolding thickness if all its unfoldings have
uniformly bounded multiplicity.
-/
def HasBoundedUnfoldingThickness
    (S : TriangulatedSurface.{u}) : Prop :=
  ∃ B : ℕ, ∀ U : Unfolding S, ∀ x : Point2, multiplicityAt U x ≤ B

/--
Main classification target.

A convex polyhedral metric on the sphere has bounded unfolding thickness iff it
is one of:
1. a disphenoid metric;
2. an edge-to-edge gluing of congruent squares;
3. an edge-to-edge gluing of congruent equilateral triangles.
-/
theorem convex_metric_bounded_unfolding_thickness_iff
    (S : TriangulatedSurface.{u})
    (hsphere : S.IsSphere)
    (hconvex : S.IsConvexMetric) :
    HasBoundedUnfoldingThickness S ↔
      S.IsDisphenoidMetric ∨
      S.IsSquareGluingMetric ∨
      S.IsEquilateralTriangleGluingMetric := by
  sorry

end Unfoldings
