module

public import Unfoldings.Cone.Neighborhood

/-!
# Constructed whole-ball cone charts

Every vertex copy of a spatially folded finite triangle complex has an
intrinsic neighborhood isometric to a ball in its constructed tangent fan.
The chart agrees with the original face coordinates on every tagged wedge
point in that ball. Its construction allows arbitrary retained seam sets.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- A whole intrinsic ball chart, preserving every original incident face coordinate. -/
structure TangentChart where
  radius : ℝ
  positive : 0 < radius
  chart : Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal radius) ≃ᵢ
    Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal radius)
  agrees : ∀ (a : C.TangentTotal retain v)
    (near : edist (C.tangentPoint retain v a) (C.tangentOrigin retain v) <
      ENNReal.ofReal radius),
    (chart ⟨C.tangentPoint retain v a, near⟩).val = C.tangentSurfaceTag retain v a

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

/-- The cone model is an actual local metric theorem, derived from the gluing construction. -/
theorem exists_tangentChart : Nonempty (C.TangentChart retain v) := by
  classical
  obtain ⟨N⟩ := F.exists_tangentNeighborhood retain v
  let coneBall := Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal N.radius)
  let surfaceBall := Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius)
  have representatives (z : coneBall) := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) z.val
  choose tag tag_eq using representatives
  change ∀ z : coneBall, C.tangentPoint retain v (tag z) = z.val at tag_eq
  have tag_near (z : coneBall) :
      edist (C.tangentOrigin retain v) (C.tangentPoint retain v (tag z)) <
        ENNReal.ofReal N.radius := by
    rw [tag_eq z, edist_comm]
    exact z.property
  have original_near (z : coneBall) :
      edist (C.vertexPoint retain v) (C.tangentSurfaceTag retain v (tag z)) <
        ENNReal.ofReal N.radius := by
    rw [F.tangentSurfaceTag_radial retain v _ (N.inside _ (tag_near z))]
    exact tag_near z
  let f : coneBall → surfaceBall := fun z =>
    ⟨C.tangentSurfaceTag retain v (tag z), by
      rw [Metric.mem_eball, edist_comm]
      exact original_near z⟩
  have iso : Isometry f := by
    intro z w
    change edist (C.tangentSurfaceTag retain v (tag z))
      (C.tangentSurfaceTag retain v (tag w)) = edist z.val w.val
    rw [N.exact_distance _ _ (tag_near z) (tag_near w), tag_eq z, tag_eq w]
  have agrees (a : C.TangentTotal retain v)
      (near : edist (C.tangentPoint retain v a) (C.tangentOrigin retain v) <
        ENNReal.ofReal N.radius) :
      (f ⟨C.tangentPoint retain v a, near⟩).val = C.tangentSurfaceTag retain v a := by
    let z : coneBall := ⟨C.tangentPoint retain v a, near⟩
    have near_a : edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) <
        ENNReal.ofReal N.radius := by rw [edist_comm]; exact near
    apply edist_eq_zero.mp
    change edist (C.tangentSurfaceTag retain v (tag z)) (C.tangentSurfaceTag retain v a) = 0
    rw [N.exact_distance _ _ (tag_near z) near_a, tag_eq z]
    exact edist_self _
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y.val
    have near_a : edist (C.vertexPoint retain v)
        (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal N.radius := by
      rw [ha, edist_comm]
      exact y.property
    obtain ⟨b, inside_b, hb⟩ := C.exists_tangentSurfaceTag_lift retain v a
      (N.incident a near_a)
    have near_b : edist (C.tangentPoint retain v b) (C.tangentOrigin retain v) <
        ENNReal.ofReal N.radius := by
      rw [edist_comm, ← F.tangentSurfaceTag_radial retain v b inside_b, hb]
      exact near_a
    refine ⟨⟨C.tangentPoint retain v b, near_b⟩, Subtype.ext ?_⟩
    exact (agrees b near_b).trans (hb.trans ha)
  let chart : coneBall ≃ᵢ surfaceBall :=
    ⟨Equiv.ofBijective f ⟨iso.injective, onto⟩, iso⟩
  exact ⟨⟨N.radius, N.positive, chart, agrees⟩⟩

/-- Choose a cone chart only after constructing it from the finite metric gluing. -/
def tangentChart : C.TangentChart retain v :=
  Classical.choice (F.exists_tangentChart retain v)

end Unfoldings.SpatialFolding
