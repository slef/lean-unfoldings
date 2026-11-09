module

public import Unfoldings.Cone.Sector

/-!
# Coordinates on a planar sector

Two independent boundary rays give coordinates on the whole complex plane.
The nonnegative quadrant maps exactly to their positive span. This supplies
closedness, convexity and genuine topological interiors for angular sectors.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The positive span of the heading-zero and heading-alpha boundary rays. -/
def planarSector (α : ℝ) : Set ℂ :=
  {z | ∃ c : ℝ, 0 ≤ c ∧ ∃ d : ℝ, 0 ≤ d ∧ z = (c : ℂ) + d • polarRay α}

/-- Real boundary-ray coordinates. -/
def sectorCombination (α : ℝ) (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + p.2 • polarRay α

/-- Independent boundary rays give a homeomorphism of the ambient planes. -/
def sectorCombinationHomeomorph (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    (ℝ × ℝ) ≃ₜ ℂ where
  toFun := sectorCombination α
  invFun z := (z.re - z.im / Real.sin α * Real.cos α, z.im / Real.sin α)
  left_inv p := by
    apply Prod.ext <;> simp only [sectorCombination, Complex.add_re, Complex.ofReal_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
      polarRay_re, Complex.add_im, Complex.mul_im, zero_add, add_zero, polarRay_im]
    · field_simp
      ring
    · exact mul_div_cancel_right₀ p.2 nonzero
  right_inv z := by
    apply Complex.ext <;> simp only [sectorCombination, Complex.add_re, Complex.ofReal_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
      polarRay_re, Complex.add_im, Complex.mul_im, zero_add, add_zero, polarRay_im]
    · ring
    · exact div_mul_cancel₀ z.im nonzero
  continuous_toFun := Complex.continuous_ofReal.comp continuous_fst |>.add
    (continuous_snd.smul continuous_const)
  continuous_invFun :=
    (Complex.continuous_re.sub ((Complex.continuous_im.div_const _).mul_const _)).prodMk
      (Complex.continuous_im.div_const _)

theorem sectorCombination_image_quadrant (α : ℝ) :
    sectorCombination α '' (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) = planarSector α := by
  ext z
  constructor
  · rintro ⟨⟨c, d⟩, inside, rfl⟩
    exact ⟨c, inside.1, d, inside.2, rfl⟩
  · rintro ⟨c, hc, d, hd, equal⟩
    exact ⟨(c, d), ⟨hc, hd⟩, equal.symm⟩

theorem isClosed_planarSector (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    IsClosed (planarSector α) := by
  rw [← sectorCombination_image_quadrant]
  exact (sectorCombinationHomeomorph α nonzero).isClosedMap _
    (isClosed_Ici.prod isClosed_Ici)

theorem convex_planarSector (α : ℝ) : Convex ℝ (planarSector α) := by
  let combination : (ℝ × ℝ) →ₗ[ℝ] ℂ :=
    (Complex.ofRealCLM.toLinearMap.comp (LinearMap.fst ℝ ℝ ℝ)) +
      ((LinearMap.snd ℝ ℝ ℝ).smulRight (polarRay α))
  have same : (combination : (ℝ × ℝ) → ℂ) = sectorCombination α := rfl
  rw [← sectorCombination_image_quadrant, ← same]
  exact (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ)) |>.linear_image combination

theorem interior_planarSector (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    interior (planarSector α) =
      {z | ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧ z = (c : ℂ) + d • polarRay α} := by
  let h := sectorCombinationHomeomorph α nonzero
  have image : h '' (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) = planarSector α :=
    sectorCombination_image_quadrant α
  rw [← image, ← h.image_interior, interior_prod_eq, interior_Ici]
  ext z
  constructor
  · rintro ⟨⟨c, d⟩, inside, equal⟩
    exact ⟨c, inside.1, d, inside.2, equal.symm⟩
  · rintro ⟨c, hc, d, hd, equal⟩
    exact ⟨(c, d), ⟨hc, hd⟩, equal.symm⟩

/-- Two supporting half-planes describe the same positive-span sector. -/
theorem mem_planarSector_iff_halfplanes (α : ℝ) (positive : 0 < Real.sin α) (z : ℂ) :
    z ∈ planarSector α ↔
      0 ≤ z.im ∧ 0 ≤ z.re * Real.sin α - z.im * Real.cos α := by
  constructor
  · rintro ⟨c, hc, d, hd, rfl⟩
    simp only [Complex.add_im, Complex.ofReal_im, Complex.real_smul, Complex.mul_im,
      zero_add, zero_mul, add_zero, polarRay_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, sub_zero, polarRay_re]
    constructor
    · exact mul_nonneg hd positive.le
    · nlinarith [mul_nonneg hc positive.le]
  · rintro ⟨imaginary, height⟩
    refine ⟨(z.re * Real.sin α - z.im * Real.cos α) / Real.sin α,
      div_nonneg height positive.le, z.im / Real.sin α,
      div_nonneg imaginary positive.le, ?_⟩
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.ofReal_re, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, polarRay_re,
        Complex.add_im, Complex.mul_im, zero_add, add_zero, polarRay_im]
    · field_simp
      ring
    · exact (div_mul_cancel₀ z.im positive.ne').symm

/-- Within the upper half-plane, sector membership is exactly the real angular interval. -/
theorem polarRay_mem_planarSector_iff (α θ : ℝ)
    (positive : 0 < α) (small : α < Real.pi) (heading : θ ∈ Set.Icc 0 Real.pi) :
    polarRay θ ∈ planarSector α ↔ θ ∈ Set.Icc 0 α := by
  have sine : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive small
  rw [mem_planarSector_iff_halfplanes α sine, polarRay_re, polarRay_im]
  have identity : Real.cos θ * Real.sin α - Real.sin θ * Real.cos α =
      Real.sin (α - θ) := by rw [Real.sin_sub]; ring
  rw [identity]
  constructor
  · rintro ⟨_, height⟩
    refine ⟨heading.1, ?_⟩
    by_contra outside
    have opposite : 0 < Real.sin (θ - α) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr (lt_of_not_ge outside)) (by linarith [heading.2])
    have negated : Real.sin (α - θ) = -Real.sin (θ - α) := by
      rw [← Real.sin_neg, neg_sub]
    rw [negated] at height
    linarith
  · intro inside
    exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi heading.1 heading.2,
      Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr inside.2) (by linarith [inside.1])⟩

/-- Every nonzero positive-span point has a real heading in the closed angular interval. -/
theorem exists_polar_of_mem_planarSector (α : ℝ) (positive : 0 < α)
    (small : α < Real.pi) (z : ℂ) (inside : z ∈ planarSector α) (nonzero : z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Icc 0 α, z = (r : ℂ) * polarRay θ := by
  have sine : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive small
  obtain ⟨imaginary, height⟩ := (mem_planarSector_iff_halfplanes α sine z).mp inside
  have norm_positive : 0 < ‖z‖ := norm_pos_iff.mpr nonzero
  have heading : z.arg ∈ Set.Icc 0 Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr imaginary, Complex.arg_le_pi z⟩
  have ray_inside : polarRay z.arg ∈ planarSector α := by
    apply (mem_planarSector_iff_halfplanes α sine _).mpr
    rw [polarRay_im, polarRay_re]
    refine ⟨Real.sin_nonneg_of_nonneg_of_le_pi heading.1 heading.2, ?_⟩
    have product : 0 ≤ ‖z‖ *
        (Real.cos z.arg * Real.sin α - Real.sin z.arg * Real.cos α) := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, Complex.norm_mul_cos_arg,
        Complex.norm_mul_sin_arg]
      exact height
    exact nonneg_of_mul_nonneg_right product norm_positive
  refine ⟨‖z‖, norm_positive, z.arg,
    (polarRay_mem_planarSector_iff α z.arg positive small heading).mp ray_inside, ?_⟩
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

end Unfoldings
