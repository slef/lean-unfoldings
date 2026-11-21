module

public import Unfoldings.Roof.CompatibleAdaptiveRouting
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Normalized slope certificates give adaptive routing in the physical roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

/-- Simultaneously scaling the progress body and the active slope does
not change the directions in the history cone. -/
theorem historyCone_image_pos_smul {r : ℝ} (positive : 0 < r) (L : Set Plane) (p : Plane) :
    historyCone ((fun x : Plane => r • x) '' L) (r • p) = historyCone L p := by
  ext d
  constructor
  · intro member x hx
    have h := member (r • x) ⟨x, hx, rfl⟩
    rw [real_inner_smul_left, real_inner_smul_left] at h
    exact (mul_le_mul_iff_of_pos_left positive).mp h
  · intro member x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [real_inner_smul_left, real_inner_smul_left]
    exact (mul_le_mul_iff_of_pos_left positive).mpr (member y hy)

end Unfoldings.SlopeEnvelope

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A normalized rim certificate can supply its supporting normal by
existence. The chosen normal and both history cone bounds survive rescaling. -/
theorem exists_compatibleAdaptiveRouting_of_scaled_rim {slopes : Set Plane}
    (convex : Convex ℝ slopes) (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    {ρ : ℝ} (scale_pos : 0 < ρ) (L : Set Plane)
    (within : L ⊆ (fun w : Plane => ρ⁻¹ • w) '' slopes)
    {r θ maxWidth η : ℝ} (r_positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    (nonnegative : 0 ≤ θ) (acute : (maxWidth + θ) / 2 < π / 2)
    (angles : ∀ f, K.normalSlope f ∈ slopes → ∀ i, (K.projectedTriangle f).cornerAngle i ≤ θ)
    (rim : ∀ p ∈ frontier ((fun w : Plane => ρ⁻¹ • w) '' slopes), ∃ n : Plane,
      ‖n‖ = 1 ∧ 0 < inner ℝ n p ∧
      (∀ w ∈ (fun w : Plane => ρ⁻¹ • w) '' slopes, inner ℝ n w ≤ inner ℝ n p) ∧
      (∃ (axis : Plane) (width : ℝ), axis ≠ 0 ∧ θ ≤ width ∧ width ≤ maxWidth ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) ∧
      ∀ z : Plane, z ∈ SlopeEnvelope.historyCone L p → η * ‖z‖ ≤ inner ℝ z n) :
    Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary ((fun w : Plane => ρ • w) '' L)
      (ρ * r) (cos ((maxWidth + θ) / 2)) η) := by
  classical
  let scaled : Set Plane := (fun w : Plane => ρ • w) '' L
  let homeo : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero scale_pos.ne')
  have undo (p : Plane) : ρ • (ρ⁻¹ • p) = p := by
    rw [smul_smul, mul_inv_cancel₀ scale_pos.ne', one_smul]
  have within_physical : scaled ⊆ slopes := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨p, hp, rfl⟩ := within hw
    change ρ • (ρ⁻¹ • p) ∈ slopes
    rwa [undo]
  have disk_physical : Metric.closedBall (0 : Plane) (ρ * r) ⊆ scaled := by
    intro p hp
    refine ⟨ρ⁻¹ • p, disk ?_, undo p⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr scale_pos), ← div_eq_inv_mul, div_le_iff₀ scale_pos]
    rw [Metric.mem_closedBall, dist_zero_right, mul_comm] at hp
    exact hp
  have geometry (p : Plane) (hp : p ∈ frontier slopes) :=
    rim (ρ⁻¹ • p) (by
      change homeo p ∈ frontier (homeo '' slopes)
      rw [← homeo.image_frontier]
      exact Set.mem_image_of_mem homeo hp)
  choose normal unit positive support cones polar using geometry
  let direction (p : Plane) := if hp : p ∈ frontier slopes then normal p hp else 0
  have same_cone (p : Plane) :
      SlopeEnvelope.historyCone scaled p = SlopeEnvelope.historyCone L (ρ⁻¹ • p) := by
    have h := SlopeEnvelope.historyCone_image_pos_smul scale_pos L (ρ⁻¹ • p)
    rw [undo] at h
    exact h
  apply K.exists_compatibleAdaptiveRouting convex compact nonempty boundary no_boundary
    scaled within_physical (mul_pos scale_pos r_positive) disk_physical nonnegative acute angles _
    direction _ _
  · intro p hp
    rw [same_cone]
    exact cones p hp
  · intro p hp
    rw [show direction p = normal p hp from dite_eq_left hp]
    refine ⟨unit p hp, ?_, ?_⟩
    · have h := positive p hp
      rw [real_inner_smul_right] at h
      exact pos_of_mul_pos_right h (inv_pos.mpr scale_pos).le
    · intro w hw
      have h := support p hp (ρ⁻¹ • w) ⟨w, hw, rfl⟩
      rw [real_inner_smul_right, real_inner_smul_right] at h
      exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr scale_pos)).mp h
  · intro p hp z hz
    rw [show direction p = normal p hp from dite_eq_left hp]
    exact polar p hp z ((same_cone p) ▸ hz)

end Unfoldings.ConvexRoof
