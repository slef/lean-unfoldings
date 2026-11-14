module

public import Unfoldings.Roof.Fenchel
public import Unfoldings.Roof.NormalCone

/-! Full primal normal cells at every interior point, without a vertex restriction. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

def pointIncidentSlopes (x : Plane) : Set Plane :=
  {p | ∃ f, x ∈ (K.projectedTriangle f).carrier ∧ K.normalSlope f = p}

theorem finite_pointIncidentSlopes (x : Plane) : (K.pointIncidentSlopes x).Finite :=
  (Set.finite_range K.normalSlope).subset (by rintro _ ⟨f, _, rfl⟩; exact ⟨f, rfl⟩)

/-- Interior subgradients are exactly the convex hull of all incident original face slopes. -/
theorem primalNormalCell_eq_incident_hull {x : Plane} (inside : x ∈ interior K.footprint) :
    K.primalNormalCell x = convexHull ℝ (K.pointIncidentSlopes x) := by
  apply Set.Subset.antisymm
  · intro p support
    by_contra outside
    obtain ⟨functional, c, below, above⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) ((K.finite_pointIncidentSlopes x).isCompact_convexHull ℝ).isClosed
      outside
    let direction := (InnerProductSpace.toDual ℝ Plane).symm functional
    have pairing (z : Plane) : inner ℝ z direction = functional z := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have star := eventually_piece_contains_center (fun f => (K.projectedTriangle f).carrier)
      (fun f => (K.projectedTriangle f).compact_carrier.isClosed) x
    have near : {y | y ∈ K.footprint ∧ ∀ f, y ∈ (K.projectedTriangle f).carrier →
        x ∈ (K.projectedTriangle f).carrier} ∈ 𝓝 x := by
      filter_upwards [star, isOpen_interior.mem_nhds inside] with y incidence interior
      exact ⟨interior_subset interior, incidence⟩
    obtain ⟨t, positive, present, incidence⟩ := exists_positive_ray_mem x direction _ near
    obtain ⟨f, face⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset present)
    have center := K.supportHeight_eq_roof_of_mem_projectedTriangle f (incidence f face)
    have endpoint := K.supportHeight_eq_roof_of_mem_projectedTriangle f face
    have ordered := support _ present
    have first : inner ℝ (x + t • direction) p = inner ℝ x p + t * functional p := by
      rw [inner_add_left, real_inner_smul_left, ← pairing]
      have comm : inner ℝ direction p = inner ℝ p direction := real_inner_comm _ _
      rw [comm]
    rw [first, ← center, ← endpoint,
      K.supportHeight_difference f x (x + t • direction)] at ordered
    have displacement : x + t • direction - x = t • direction := by abel
    rw [displacement, inner_smul_right, pairing] at ordered
    have slope := below _ (subset_convexHull ℝ _
      (show K.normalSlope f ∈ K.pointIncidentSlopes x from ⟨f, incidence f face, rfl⟩))
    nlinarith
  · apply convexHull_min ?_ (K.convex_primalNormalCell x)
    rintro _ ⟨f, member, rfl⟩
    exact K.original_slope_mem_primalNormalCell f member

/-- A bounded full normal cell rules out an original rim point. -/
theorem interior_of_bounded_primalNormalCell {x : Plane} (member : x ∈ K.footprint)
    (bounded : Bornology.IsBounded (K.primalNormalCell x)) : x ∈ interior K.footprint := by
  by_contra outside
  obtain ⟨L, nonzero, support⟩ := geometric_hahn_banach_of_nonempty_interior_point
    K.convex_projection outside K.interior_projection
  let d := (InnerProductSpace.toDual ℝ Plane).symm L
  have pairing (y : Plane) : inner ℝ y d = L y := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have dne : d ≠ 0 := by
    intro zero
    apply nonzero
    ext y
    have equal := pairing y
    rw [zero, inner_zero_right] at equal
    exact equal.symm
  obtain ⟨p, normal⟩ := K.primalNormalCell_nonempty member
  have ray (t : ℝ) (ht : 0 ≤ t) : p + t • d ∈ K.primalNormalCell x := by
    intro y hy
    have old := normal y hy
    have bound := support y hy
    simp only [inner_add_right, real_inner_smul_right, pairing]
    nlinarith
  obtain ⟨B, positive, bound⟩ := bounded.exists_pos_norm_le
  let t := (B + ‖p‖ + 1) / ‖d‖
  have tpos : 0 < t := div_pos (by positivity) (norm_pos_iff.mpr dne)
  have growth : ‖t • d‖ = B + ‖p‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg tpos.le]
    dsimp [t]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr dne)
  have inequality : ‖t • d‖ ≤ B + ‖p‖ := by
    calc
      _ = ‖(p + t • d) - p‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖p + t • d‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ B + ‖p‖ := by linarith [bound _ (ray t tpos.le)]
  linarith

end Unfoldings.ConvexRoof
