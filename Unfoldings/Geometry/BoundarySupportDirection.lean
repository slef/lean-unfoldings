module

public import Unfoldings.Basic
public import Unfoldings.Geometry.AffineMaximum
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Deterministic unit outward directions at every boundary slope of a convex body. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem exists_unit_boundary_support_direction {K : Set Plane} (convex : Convex ℝ K)
    (origin : (0 : Plane) ∈ interior K) {p : Plane} (boundary : p ∈ frontier K) :
    ∃ u : Plane, ‖u‖ = 1 ∧ 0 < inner ℝ u p ∧ ∀ q ∈ K, inner ℝ u q ≤ inner ℝ u p := by
  obtain ⟨L, nonzero, support⟩ := geometric_hahn_banach_of_nonempty_interior_point
    convex boundary.2 ⟨0, origin⟩
  let n := (InnerProductSpace.toDual ℝ Plane).symm L
  have pairing (q : Plane) : inner ℝ n q = L q := InnerProductSpace.toDual_symm_apply
  have nne : n ≠ 0 := by
    intro zero
    apply nonzero
    ext q
    have equal := pairing q
    rw [zero, inner_zero_left] at equal
    exact equal.symm
  have strict : 0 < L p := by
    have below := supporting_functional_lt_on_interior L nonzero K (L p) support 0 origin
    simpa only [map_zero] using below
  refine ⟨NormedSpace.normalize n, NormedSpace.norm_normalize nne, ?_, ?_⟩
  · change 0 < inner ℝ (‖n‖⁻¹ • n) p
    rw [real_inner_smul_left, pairing]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr nne)) strict
  · intro q hq
    change inner ℝ (‖n‖⁻¹ • n) q ≤ inner ℝ (‖n‖⁻¹ • n) p
    rw [real_inner_smul_left, real_inner_smul_left, pairing, pairing]
    exact mul_le_mul_of_nonneg_left (support q hq) (inv_nonneg.mpr (norm_nonneg _))

open Classical in
/-- One globally fixed choice handles corner slopes consistently at every root and merger. -/
def boundarySupportDirection {K : Set Plane} (convex : Convex ℝ K)
    (origin : (0 : Plane) ∈ interior K) (p : Plane) : Plane :=
  if boundary : p ∈ frontier K then
    (exists_unit_boundary_support_direction convex origin boundary).choose else 0

theorem boundarySupportDirection_spec {K : Set Plane} (convex : Convex ℝ K)
    (origin : (0 : Plane) ∈ interior K) {p : Plane} (boundary : p ∈ frontier K) :
    ‖boundarySupportDirection convex origin p‖ = 1 ∧
      0 < inner ℝ (boundarySupportDirection convex origin p) p ∧
        ∀ q ∈ K, inner ℝ (boundarySupportDirection convex origin p) q ≤
          inner ℝ (boundarySupportDirection convex origin p) p := by
  classical
  rw [boundarySupportDirection, dite_eq_left boundary]
  exact (exists_unit_boundary_support_direction convex origin boundary).choose_spec

end Unfoldings
