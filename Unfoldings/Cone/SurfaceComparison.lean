module

public import Unfoldings.Cone.SurfaceTags
public import Unfoldings.Metric.LocalMap

/-!
# Local metric comparison from tangent fans to surfaces

Inside a sufficiently small vertex neighborhood, the actual bounded triangles
contain every relevant tangent wedge point. Short routes in the tangent fan
therefore give routes of at most the same length in the original surface.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem tangentSurfaceTag_step (a b : C.TangentTotal retain v)
    (inside_a : a.2.val ∈ (C.triangle a.1.val.1).carrier)
    (inside_b : b.2.val ∈ (C.triangle b.1.val.1).carrier) :
    edist (C.tangentSurfaceTag retain v a) (C.tangentSurfaceTag retain v b) ≤
      MetricGluing.stepCost (C.TangentCell retain v) (C.tangentGlue retain v) a b := by
  classical
  by_cases joined : C.tangentGlue retain v a b ∨ C.tangentGlue retain v b a
  · have equal := joined.elim
      (fun h => F.tangentSurfaceTag_glue retain v a b h inside_a inside_b)
      (fun h => (F.tangentSurfaceTag_glue retain v b a h inside_b inside_a).symm)
    simp [MetricGluing.stepCost, joined, equal]
  · obtain ⟨c, x⟩ := a
    obtain ⟨d, y⟩ := b
    by_cases same : c = d
    · subst d
      rw [C.tangentSurfaceTag_of_mem retain v _ inside_a,
        C.tangentSurfaceTag_of_mem retain v _ inside_b]
      simp only [MetricGluing.stepCost, joined, ite_false,
        MetricGluing.faceCost, dite_true]
      change edist (C.faceMap retain c.val.1 ⟨x.val, inside_a⟩)
        (C.faceMap retain c.val.1 ⟨y.val, inside_b⟩) ≤ edist x.val y.val
      have equal := (F.faceMap_isometry retain c.val.1).edist_eq
        (⟨x.val, inside_a⟩ : C.Cell c.val.1) ⟨y.val, inside_b⟩
      change edist (C.faceMap retain c.val.1 ⟨x.val, inside_a⟩)
        (C.faceMap retain c.val.1 ⟨y.val, inside_b⟩) = edist x.val y.val at equal
      exact equal.le
    · simp [MetricGluing.stepCost, joined, MetricGluing.faceCost, same]

/-- The canonical tagged map is nonexpanding on some whole tangent neighborhood. -/
theorem exists_tangentSurfaceTag_edist_le :
    ∃ r > 0, (∀ a : C.TangentTotal retain v,
      edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) < ENNReal.ofReal r →
        a.2.val ∈ (C.triangle a.1.val.1).carrier) ∧
      ∀ a b : C.TangentTotal retain v,
        edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) < ENNReal.ofReal r →
        edist (C.tangentOrigin retain v) (C.tangentPoint retain v b) < ENNReal.ofReal r →
        edist (C.tangentSurfaceTag retain v a) (C.tangentSurfaceTag retain v b) ≤
          edist (C.tangentPoint retain v a) (C.tangentPoint retain v b) := by
  obtain ⟨δ, δpos, inside⟩ := C.exists_tangent_triangle_radius retain v
  let r := δ / 3
  have rpos : 0 < r := div_pos δpos (by norm_num)
  have small : r ≤ δ := by dsimp [r]; linarith
  have local_step (a b : C.TangentTotal retain v)
      (ha : edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) <
        ENNReal.ofReal δ)
      (hb : edist (C.tangentOrigin retain v) (C.tangentPoint retain v b) <
        ENNReal.ofReal δ) := F.tangentSurfaceTag_step retain v a b (inside _ _ ha) (inside _ _ hb)
  have restricted (a : C.TangentTotal retain v)
      (ha : edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) <
        ENNReal.ofReal r) : a.2.val ∈ (C.triangle a.1.val.1).carrier :=
    inside _ _ (ha.trans_le (ENNReal.ofReal_le_ofReal small))
  refine ⟨r, rpos, restricted, ?_⟩
  intro a b ha hb
  have radial_a := F.tangentSurfaceTag_radial retain v a (restricted a ha)
  have radial_b := F.tangentSurfaceTag_radial retain v b (restricted b hb)
  have left : edist (C.tangentSurfaceTag retain v a) (C.vertexPoint retain v) <
      ENNReal.ofReal r := by rw [edist_comm, radial_a]; exact ha
  have right : edist (C.vertexPoint retain v) (C.tangentSurfaceTag retain v b) <
      ENNReal.ofReal r := by rw [radial_b]; exact hb
  have chord := (edist_triangle (C.tangentSurfaceTag retain v a)
    (C.vertexPoint retain v) (C.tangentSurfaceTag retain v b)).trans_lt
      (ENNReal.add_lt_add left right)
  have total := ENNReal.add_lt_add ha chord
  have radius_sum : ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) =
      ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add rpos.le rpos.le,
      ← ENNReal.ofReal_add rpos.le (add_nonneg rpos.le rpos.le)]
    congr 1
    dsimp [r]
    ring
  rw [radius_sum] at total
  exact MetricGluing.map_edist_le_edist_of_budget
    (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentSurfaceTag retain v) (C.tangentOrigin retain v) (ENNReal.ofReal δ)
    local_step a b total

end Unfoldings.SpatialFolding
