module

public import Unfoldings.Geometry.StereographicConvex

/-! The centered stereographic chart and its exact spherical inverse. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- Stereographic coordinates from the south pole with unit equatorial radius. -/
def stereographicCoord (u : Space) : Plane :=
  (1 + u 2)⁻¹ • horizontal u

theorem norm_sq_stereographicCoord {u : Space} (unit : ‖u‖ = 1) (height : -1 < u 2) :
    ‖stereographicCoord u‖ ^ 2 = (1 - u 2) / (1 + u 2) := by
  have den : 0 < 1 + u 2 := by linarith
  have horizontal_sq : ‖horizontal u‖ ^ 2 = 1 - (u 2) ^ 2 := by
    have h := horizontal_norm_sq u
    rw [unit, one_pow] at h
    linarith
  rw [stereographicCoord, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr den.le),
    mul_pow, horizontal_sq]
  field_simp [den.ne']
  ring

theorem stereographicCoord_inverseStereographic (x : Plane) :
    stereographicCoord (inverseStereographic x) = x := by
  rw [stereographicCoord, inverseStereographic_height, horizontal_inverseStereographic, smul_smul]
  have d : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  rw [show (1 + (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2))⁻¹ * (2 / (1 + ‖x‖ ^ 2)) = 1 by
    rw [show 1 + (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2) = 2 / (1 + ‖x‖ ^ 2) by
      field_simp [d]; ring]
    exact inv_mul_cancel₀ (div_ne_zero (by norm_num) d), one_smul]

theorem inverseStereographic_stereographicCoord {u : Space} (unit : ‖u‖ = 1) (height : -1 < u 2) :
    inverseStereographic (stereographicCoord u) = u := by
  have d : 1 + u 2 ≠ 0 := by linarith
  have denom : 1 + ‖stereographicCoord u‖ ^ 2 = 2 / (1 + u 2) := by
    rw [norm_sq_stereographicCoord unit height]
    field_simp [d]
    ring
  have h : horizontal (inverseStereographic (stereographicCoord u)) = horizontal u := by
    rw [horizontal_inverseStereographic, denom, div_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      stereographicCoord, smul_smul, mul_inv_cancel₀ d, one_smul]
  have k : inverseStereographic (stereographicCoord u) 2 = u 2 := by
    rw [inverseStereographic_height, denom, norm_sq_stereographicCoord unit height]
    field_simp [d]
    ring
  ext i
  fin_cases i
  · exact congrArg (fun x : Plane => x 0) h
  · exact congrArg (fun x : Plane => x 1) h
  · exact k

/-- A region given by hemispheres through or containing the north pole
and lying in the open hemisphere projects to a convex subset of the unit disk. -/
theorem stereographicCoord_image_region {I : Sort*} (normal : I → Space)
    (center : ∀ i, 0 ≤ normal i 2)
    (north : ∀ u : Space, ‖u‖ = 1 → (∀ i, 0 ≤ inner ℝ (normal i) u) → 0 < u 2) :
    Convex ℝ (stereographicCoord ''
      {u | ‖u‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) u}) ∧
    stereographicCoord '' {u | ‖u‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) u} ⊆ Metric.ball 0 1 := by
  have equal : stereographicCoord '' {u | ‖u‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) u} =
      {x | ∀ i, 0 ≤ inner ℝ (normal i) (inverseStereographic x)} := by
    ext x
    constructor
    · rintro ⟨u, ⟨hu, hN⟩, rfl⟩
      rw [Set.mem_ofPred_eq, inverseStereographic_stereographicCoord hu (by linarith [north u hu hN])]
      exact hN
    · intro hx
      exact ⟨inverseStereographic x, ⟨inverseStereographic_unit x, hx⟩,
        stereographicCoord_inverseStereographic x⟩
  rw [equal]
  refine ⟨convex_inverseStereographic_region normal center, ?_⟩
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact (inverseStereographic_upward_iff x).mp
    (north _ (inverseStereographic_unit x) hx)

end Unfoldings.Cap
