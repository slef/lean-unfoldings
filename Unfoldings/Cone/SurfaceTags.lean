module

public import Unfoldings.Cone.Spatial
public import Unfoldings.Complex.EmbeddedStars
public import Unfoldings.Geometry.CornerEdges

/-!
# Local maps from tangent wedges to the original cut surface

A uniform positive radius puts every tangent wedge point back inside its
original bounded triangle. On these pieces the original face maps preserve
radial distance, and tangent seam identifications are original retained seam
identifications.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

abbrev TangentTotal := MetricGluing.Total (C.TangentCell retain v)

abbrev tangentPoint (a : C.TangentTotal retain v) : C.TangentFan retain v :=
  MetricGluing.point (C.TangentCell retain v) (C.tangentGlue retain v) a

theorem vertexPoint_eq_cornerAt (c : C.CornerAt retain v) :
    C.vertexPoint retain v = C.faceMap retain c.val.1
      ⟨(C.triangle c.val.1).vertex c.val.2, (C.triangle c.val.1).vertex_mem c.val.2⟩ :=
  (congrArg (C.vertexPoint retain) c.property).symm

/-- A positive common radius where all actual wedges agree with the original triangles. -/
theorem exists_tangent_triangle_radius : ∃ r > 0, ∀ c, ∀ x : C.TangentCell retain v c,
    edist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) < ENNReal.ofReal r →
      x.val ∈ (C.triangle c.val.1).carrier := by
  have radii (c : C.CornerAt retain v) :=
    (C.triangle c.val.1).exists_ball_cornerWedge c.val.2
  choose radius positive wedge using radii
  obtain ⟨r, rpos, small⟩ := MetricBarrier.exists_pos_le_of_finite radius positive
  refine ⟨r, rpos, ?_⟩
  intro c x near
  have close : dist x.val ((C.triangle c.val.1).vertex c.val.2) < r := by
    rw [C.tangent_edist_origin_faceMap, edist_dist, dist_comm] at near
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp near
  exact (wedge c x.val (Metric.mem_ball.mpr (close.trans_le (small c)))).mpr x.property

/-- The original triangle map where available; outside it this tagged map takes the vertex value. -/
def tangentSurfaceTag (a : C.TangentTotal retain v) : C.Realization retain := by
  classical
  exact if inside : a.2.val ∈ (C.triangle a.1.val.1).carrier then
    C.faceMap retain a.1.val.1 ⟨a.2.val, inside⟩ else C.vertexPoint retain v

theorem tangentSurfaceTag_of_mem (a : C.TangentTotal retain v)
    (inside : a.2.val ∈ (C.triangle a.1.val.1).carrier) :
    C.tangentSurfaceTag retain v a = C.faceMap retain a.1.val.1 ⟨a.2.val, inside⟩ := by
  simp only [tangentSurfaceTag, dite_eq_left inside]

theorem tangentLeftPoint_mem_edge (s : C.TangentSeam retain v) (x : C.TangentDomain retain v s)
    (t : ℝ) (nonnegative : 0 ≤ t)
    (inside : (C.tangentLeftPoint retain v s x t nonnegative).val ∈
      (C.triangle (C.seamSide s.val.1 s.val.2.1).face).carrier) :
    (C.tangentLeftPoint retain v s x t nonnegative).val ∈
      (C.triangle (C.seamSide s.val.1 s.val.2.1).face).edge
        (C.seamSide s.val.1 s.val.2.1).edge := by
  change AffineMap.lineMap
    (C.tangentApex retain v (C.tangentLeft retain v s)).val x.val t ∈ _ at inside ⊢
  rw [C.tangentLeft_apex_endpoint retain v s] at inside ⊢
  exact Triangle.lineMap_mem_edge_of_mem_carrier _ _ _ x t inside

theorem tangentRightPoint_mem_edge (s : C.TangentSeam retain v) (x : C.TangentDomain retain v s)
    (t : ℝ) (nonnegative : 0 ≤ t)
    (inside : (C.tangentRightPoint retain v s x t nonnegative).val ∈
      (C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).carrier) :
    (C.tangentRightPoint retain v s x t nonnegative).val ∈
      (C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).edge
        (C.seamSide s.val.1 (!s.val.2.1)).edge := by
  change AffineMap.lineMap (C.tangentApex retain v (C.tangentRight retain v s)).val
    (C.across s.val.1 s.val.2.1 x).val t ∈ _ at inside ⊢
  rw [C.tangentRight_apex_endpoint retain v s] at inside ⊢
  exact Triangle.lineMap_mem_edge_of_mem_carrier _ _ _ _ t inside

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

/-- The original cut surface and tangent fan have identical radial distances on a common piece. -/
theorem tangentSurfaceTag_radial (a : C.TangentTotal retain v)
    (inside : a.2.val ∈ (C.triangle a.1.val.1).carrier) :
    edist (C.vertexPoint retain v) (C.tangentSurfaceTag retain v a) =
      edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) := by
  obtain ⟨c, x⟩ := a
  rw [C.tangentSurfaceTag_of_mem retain v _ inside, C.vertexPoint_eq_cornerAt retain v c]
  let apex : C.Cell c.val.1 :=
    ⟨(C.triangle c.val.1).vertex c.val.2, (C.triangle c.val.1).vertex_mem c.val.2⟩
  let original : C.Cell c.val.1 := ⟨x.val, inside⟩
  change edist (C.faceMap retain c.val.1 apex) (C.faceMap retain c.val.1 original) = _
  calc
    _ = edist apex original := (F.faceMap_isometry retain c.val.1).edist_eq apex original
    _ = edist (C.tangentApex retain v c) x := rfl
    _ = _ := (C.tangent_edist_origin_faceMap retain v c x).symm

theorem tangentSurfaceTag_glue (a b : C.TangentTotal retain v)
    (joined : C.tangentGlue retain v a b)
    (inside_a : a.2.val ∈ (C.triangle a.1.val.1).carrier)
    (inside_b : b.2.val ∈ (C.triangle b.1.val.1).carrier) :
    C.tangentSurfaceTag retain v a = C.tangentSurfaceTag retain v b := by
  obtain ⟨s, x, t, nonnegative, rfl, rfl⟩ := joined
  let p := C.tangentLeftPoint retain v s x t nonnegative
  let q := C.tangentRightPoint retain v s x t nonnegative
  let edge : C.TangentDomain retain v s := ⟨p.val,
    C.tangentLeftPoint_mem_edge retain v s x t nonnegative inside_a⟩
  have spatial : F.place (C.seamSide s.val.1 s.val.2.1).face p.val =
      F.place (C.seamSide s.val.1 (!s.val.2.1)).face q.val :=
    F.tangentCellToSpace_compatible retain v _ _ ⟨s, x, t, nonnegative, rfl, rfl⟩
  have coordinates : (C.across s.val.1 s.val.2.1 edge).val = q.val :=
    (F.place (C.seamSide s.val.1 (!s.val.2.1)).face).injective
      ((F.place_across s.val.1 s.val.2.1 edge).symm.trans spatial)
  have crossing : C.Crosses retain
      ⟨(C.seamSide s.val.1 s.val.2.1).face, ⟨p.val, inside_a⟩⟩
      ⟨(C.seamSide s.val.1 (!s.val.2.1)).face, ⟨q.val, inside_b⟩⟩ := by
    refine ⟨s.val.1, s.property.1, s.val.2.1, edge, rfl, ?_⟩
    apply congrArg (Sigma.mk (C.seamSide s.val.1 (!s.val.2.1)).face)
    exact Subtype.ext coordinates.symm
  rw [C.tangentSurfaceTag_of_mem retain v _ inside_a,
    C.tangentSurfaceTag_of_mem retain v _ inside_b]
  rcases (C.crosses_iff retain _ _).mp crossing with forward | backward
  · exact MetricGluing.point_eq_of_glue C.Cell forward
  · exact (MetricGluing.point_eq_of_glue C.Cell backward).symm

end Unfoldings.SpatialFolding
