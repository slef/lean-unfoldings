import Unfoldings.GlueSpace

/-!
# Triangulated surfaces from Euclidean triangles and edge gluings

This file gives a second, more concrete scaffold for triangulated surfaces.
Instead of taking vertices, edges, and faces as independent combinatorial data,
we start with finitely many Euclidean triangles and specify which triangle edges
are glued.

The metric-space construction is routed through `Unfoldings.GlueSpace`, a
generic n-ary gluing scaffold for a family of metric spaces with declared
isometric overlap charts.
-/

noncomputable section

namespace Unfoldings
namespace Gluing

universe u

/-- The Euclidean plane. -/
abbrev Point2 : Type := EuclideanSpace ℝ (Fin 2)

/--
A Euclidean triangle, represented by its three vertices in the Euclidean plane.

The current scaffold deliberately keeps degeneracy assumptions separate from
the raw data: a later file can add predicates such as affine independence or
positive area without changing the basic gluing interface.
-/
structure EuclideanTriangle where
  /-- The three vertices of the triangle. -/
  vertex : Fin 3 → Point2

namespace EuclideanTriangle

/-- The first endpoint of the numbered edge of a triangle. -/
def edgeStart : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- The second endpoint of the numbered edge of a triangle. -/
def edgeEnd : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The two endpoint indices of an edge, as an unordered pair. -/
def edgeVerts (e : Fin 3) : Sym2 (Fin 3) :=
  s(edgeStart e, edgeEnd e)

/-- The Euclidean length of an edge of a triangle. -/
def edgeLength (T : EuclideanTriangle) (e : Fin 3) : ℝ :=
  dist (T.vertex (edgeStart e)) (T.vertex (edgeEnd e))

/-- The closed triangular metric subspace spanned by the three vertices. -/
abbrev Space (T : EuclideanTriangle) : Set Point2 :=
  convexHull ℝ (Set.range T.vertex)

/-- The closed edge-segment metric subspace corresponding to one edge. -/
abbrev EdgeSpace (T : EuclideanTriangle) (e : Fin 3) : Set Point2 :=
  segment ℝ (T.vertex (edgeStart e)) (T.vertex (edgeEnd e))

end EuclideanTriangle

/-- A reference to one of the three edges of one face. -/
structure EdgeRef (Face : Type u) where
  /-- The triangle containing the edge. -/
  face : Face
  /-- The local edge number inside that triangle. -/
  edge : Fin 3

namespace EdgeRef

variable {Face : Type u} (tri : Face → EuclideanTriangle)

/-- The length of a referenced triangle edge. -/
def length (e : EdgeRef Face) : ℝ :=
  (tri e.face).edgeLength e.edge

/-- The metric subspace carried by a referenced triangle edge. -/
abbrev Space (e : EdgeRef Face) : Type :=
  (tri e.face).EdgeSpace e.edge

end EdgeRef

/-- An unordered pair of triangle-edge references. -/
abbrev EdgePair (Face : Type u) : Type u :=
  Sym2 (EdgeRef Face)

namespace EdgePair

variable {Face : Type u} (tri : Face → EuclideanTriangle)

/-- The two referenced edges in an edge pair have the same Euclidean length. -/
def SameLength : EdgePair Face → Prop :=
  Sym2.lift
    ⟨fun e₁ e₂ => e₁.length tri = e₂.length tri, by
      intro e₁ e₂
      exact propext eq_comm⟩

@[simp]
theorem sameLength_mk (e₁ e₂ : EdgeRef Face) :
    SameLength tri s(e₁, e₂) ↔ e₁.length tri = e₂.length tri :=
  Iff.rfl

end EdgePair

/--
A triangulated surface described by Euclidean triangles and edge identifications.

The gluing relation is a set of unordered pairs of triangle edges.  The fields
enforce the two basic consistency conditions requested here:
* glued edges have equal Euclidean length;
* each edge occurs in at most one gluing pair.
-/
structure TriangulatedSurface where
  /-- The finite set of triangular faces. -/
  Face : Type u
  [fintypeFace : Fintype Face]
  /-- A Euclidean triangle for each face. -/
  triangle : Face → EuclideanTriangle
  /-- Unordered pairs of triangle edges to identify. -/
  gluings : Set (EdgePair Face)
  /-- A gluing pair is never the same edge paired with itself. -/
  not_diag : ∀ p ∈ gluings, ¬ p.IsDiag
  /-- Glued edges have the same Euclidean length. -/
  same_length : ∀ p ∈ gluings, EdgePair.SameLength triangle p
  /-- Each triangle edge appears in at most one gluing pair. -/
  edge_mem_unique :
    ∀ e : EdgeRef Face, ∀ p ∈ gluings, ∀ q ∈ gluings, e ∈ p → e ∈ q → p = q

attribute [instance] TriangulatedSurface.fintypeFace

namespace TriangulatedSurface

variable (S : TriangulatedSurface.{u})

/-- Edge references of a triangulated surface. -/
abbrev Edge : Type u :=
  EdgeRef S.Face

/-- Edge pairs of a triangulated surface. -/
abbrev Pair : Type u :=
  EdgePair S.Face

/-- The length of an edge in a triangulated surface. -/
def edgeLength (e : S.Edge) : ℝ :=
  e.length S.triangle

/-- The metric subspace carried by an edge of a triangulated surface. -/
abbrev EdgeSpace (e : S.Edge) : Type :=
  e.Space S.triangle

/-- An edge is glued if it belongs to one of the gluing pairs. -/
def IsGluedEdge (e : S.Edge) : Prop :=
  ∃ p ∈ S.gluings, e ∈ p

/-- Boundary edges are precisely those not used by any gluing pair. -/
def IsBoundaryEdge (e : S.Edge) : Prop :=
  ¬ S.IsGluedEdge e

/-- A gluing pair contains an edge of a specified face. -/
def PairHasFace (p : S.Pair) (f : S.Face) : Prop :=
  ∃ e : S.Edge, e.face = f ∧ e ∈ p

/-- A point of a triangle lies on one of its local edges. -/
def PointOnEdge (f : S.Face) (e : Fin 3) (x : (S.triangle f).Space) : Prop :=
  (x : Point2) ∈ (S.triangle f).EdgeSpace e

/-- The disjoint union of the triangle metric spaces before any edge identifications. -/
abbrev DisjointTriangleSpace : Type u :=
  Σ f : S.Face, (S.triangle f).Space

end TriangulatedSurface

/-!
## All-at-once gluing through `Unfoldings.GlueSpace`

Every declared edge pair becomes one overlap chart in a single disjoint-union
quotient.
-/

/--
Metric data realizing one unordered edge pair of a triangulated surface.

The unordered pair is represented by an ordered pair of edge references only
for the purpose of naming the two maps required by `GlueSpace.Data`.
-/
structure PairIdentification (S : TriangulatedSurface.{u}) (p : S.Pair) where
  /-- First edge of the ordered representative. -/
  left : S.Edge
  /-- Second edge of the ordered representative. -/
  right : S.Edge
  /-- The ordered representative is the given unordered edge pair. -/
  pair_eq : p = s(left, right)
  /-- Common metric parameter space for the two glued edges. -/
  Param : Type
  [metricSpaceParam : MetricSpace Param]
  /-- Parametrization of the first edge inside its triangle. -/
  leftMap : Param → (S.triangle left.face).Space
  /-- Parametrization of the second edge inside its triangle. -/
  rightMap : Param → (S.triangle right.face).Space
  /-- The first parametrization is isometric. -/
  left_isometry : Isometry leftMap
  /-- The second parametrization is isometric. -/
  right_isometry : Isometry rightMap

attribute [instance] PairIdentification.metricSpaceParam

/-- Choices of metric edge-identification data for all declared gluing pairs. -/
structure SurfaceGlueData (S : TriangulatedSurface.{u}) where
  /-- Metric realization of each declared gluing pair. -/
  identify : ∀ p : { p : S.Pair // p ∈ S.gluings }, PairIdentification S p.1

namespace SurfaceGlueData

variable {S : TriangulatedSurface.{u}} (G : SurfaceGlueData S)

/-- The generic n-ary gluing data associated to a triangulated surface. -/
def toGlueData : GlueSpace.Data where
  I := S.Face
  E := fun f => (S.triangle f).Space
  J := { p : S.Pair // p ∈ S.gluings }
  left := fun p => (G.identify p).left.face
  right := fun p => (G.identify p).right.face
  Param := fun p => (G.identify p).Param
  leftMap := fun p => (G.identify p).leftMap
  rightMap := fun p => (G.identify p).rightMap
  left_isometry := fun p => (G.identify p).left_isometry
  right_isometry := fun p => (G.identify p).right_isometry

end SurfaceGlueData

/--
An all-at-once metric realization of a triangulated surface.

`data` records the edge parametrizations.  `metric` is the pseudometric on the
disjoint union satisfying the generic n-ary gluing axioms; its separation
quotient is the resulting metric space.
-/
structure SurfaceMetricGluing (S : TriangulatedSurface.{u}) where
  /-- N-ary edge-gluing data for all declared pairs. -/
  data : SurfaceGlueData S
  /-- Metric realization of the n-ary gluing data. -/
  metric : GlueSpace.MetricData data.toGlueData

namespace SurfaceMetricGluing

/-- The metric space obtained by all-at-once gluing of the triangulated surface. -/
abbrev Space {S : TriangulatedSurface.{u}} (G : SurfaceMetricGluing S) : Type u :=
  GlueSpace.Space (G.data).toGlueData G.metric

instance {S : TriangulatedSurface.{u}} (G : SurfaceMetricGluing S) : MetricSpace (Space G) :=
  inferInstance

/-- The canonical map from a triangle into the all-at-once glued metric space. -/
def faceMap {S : TriangulatedSurface.{u}} (G : SurfaceMetricGluing S) (f : S.Face) :
    (S.triangle f).Space → Space G :=
  GlueSpace.of (G.data).toGlueData G.metric f

/-- Each triangle maps isometrically into the all-at-once glued metric space. -/
theorem faceMap_isometry {S : TriangulatedSurface.{u}} (G : SurfaceMetricGluing S) (f : S.Face) :
    Isometry (faceMap G f) :=
  GlueSpace.isometry_of (G.data).toGlueData G.metric f

/-- Each declared edge parametrization pair is identified in the glued metric space. -/
theorem edge_glued_eq {S : TriangulatedSurface.{u}} (G : SurfaceMetricGluing S)
    (p : { p : S.Pair // p ∈ S.gluings })
    (z : (G.data.identify p).Param) :
    faceMap G (G.data.identify p).left.face ((G.data.identify p).leftMap z) =
      faceMap G (G.data.identify p).right.face ((G.data.identify p).rightMap z) :=
  GlueSpace.of_glued_eq (G.data).toGlueData G.metric p z

end SurfaceMetricGluing

end Gluing
end Unfoldings
