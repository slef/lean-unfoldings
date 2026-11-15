module

public import Unfoldings.Geometry.TwoBankAngle

/-! Construct actual two-bank Jordan gaps by an ambient homeomorphism of the plane. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- Both exact polygonal banks are obtained from the boundary of one fixed right-angle sector. -/
def twoBankFrame : ℂ ≃ₜ ℂ :=
  (variableSectorHomeomorph (Real.pi / 2) (by simp)
    (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero)
    (R.sin_twoBankAngle_ne_zero Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)
    (R.continuousOn_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)).trans (R.bankFrame first_outward first_nonzero)

@[simp] theorem twoBankFrame_real (r : ℝ≥0) :
    R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero positive_phase (r : ℂ) =
      R.radialPoint first_outward first_nonzero r := by
  change R.bankFrame first_outward first_nonzero
    (variableSectorHomeomorph _ _ _ _ _ (r : ℂ)) = _
  rw [variableSectorHomeomorph_real, R.bankFrame_real]

include positive_phase in
/-- The final boundary retains the second actual bank, including its source and infinite tail. -/
theorem twoBankFrame_upper (common : Q.start = R.start) (r : ℝ≥0) :
    R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero positive_phase
      (polarRay (Real.pi / 2) * (r : ℂ)) = Q.radialPoint last_outward last_nonzero r := by
  change R.bankFrame first_outward first_nonzero (variableSectorHomeomorph _ _ _ _ _
    (polarRay (Real.pi / 2) * (r : ℂ))) = _
  rw [variableSectorHomeomorph_upper]
  by_cases zero : r = 0
  · subst r
    simp only [NNReal.coe_zero, Complex.ofReal_zero, mul_zero, R.bankFrame_apply,
      nnnorm_zero, mul_zero, add_zero, Q.radialPoint_zero, common]
  · have positive : 0 < r := lt_of_le_of_ne zero_le (Ne.symm zero)
    have radius : ‖polarRay
        (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r) *
          (r : ℂ)‖₊ = r := by
      apply NNReal.eq
      simp only [coe_nnnorm, norm_mul, norm_polarRay, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    rw [R.bankFrame_apply, radius,
      R.polarRay_twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r positive]
    have denominator : R.radialCoefficient first_outward first_nonzero r ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [R.radialCoefficient_unit first_outward first_nonzero r positive]
      exact one_ne_zero
    have phase : R.radialCoefficient first_outward first_nonzero r *
        (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r * (r : ℂ)) =
          Q.radialCoefficient last_outward last_nonzero r * (r : ℂ) := by
      unfold twoBankRatio
      field_simp
    rw [phase]
    change R.start + (Q.radialPoint last_outward last_nonzero r - Q.start) / (r : ℂ) *
      (r : ℂ) = Q.radialPoint last_outward last_nonzero r
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (show (0 : ℝ) < r from positive).ne'), common]
    abel

/-- The gap is the actual ambient sector image, rather than a nonoverlap certificate. -/
def twoBankGap : Set ℂ :=
  R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero positive_phase ''
    planarSector (Real.pi / 2)

theorem isClosed_twoBankGap :
    IsClosed (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase) :=
  (R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
    positive_phase).isClosedMap _
    (isClosed_planarSector (Real.pi / 2) (by simp))

/-- The exact original and final banks are the whole frontier, including the unbounded ends. -/
theorem frontier_twoBankGap (common : Q.start = R.start) :
    frontier (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) =
      R.carrier ∪ Q.carrier := by
  rw [twoBankGap, ← (R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
    positive_phase).image_frontier, frontier_planarSector (Real.pi / 2) (by simp),
    Set.image_union, ← Set.range_comp, ← Set.range_comp]
  simp only [Function.comp_def, R.twoBankFrame_real, R.twoBankFrame_upper Q first_outward
    first_nonzero last_outward last_nonzero positive_phase common]
  rw [R.range_radialPoint, Q.range_radialPoint]

include first_outward first_nonzero last_outward last_nonzero positive_phase in
/-- The two exact frontier banks share only their source. -/
theorem twoBank_carriers_inter (common : Q.start = R.start) :
    R.carrier ∩ Q.carrier = {R.start} := by
  ext z
  constructor
  · rintro ⟨first_member, last_member⟩
    rw [← R.range_radialPoint first_outward first_nonzero] at first_member
    rw [← Q.range_radialPoint last_outward last_nonzero] at last_member
    obtain ⟨r, rfl⟩ := first_member
    obtain ⟨s, equal⟩ := last_member
    have same : R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
        positive_phase (r : ℂ) =
      R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero positive_phase
        (polarRay (Real.pi / 2) * (s : ℂ)) := by
      rw [R.twoBankFrame_real, R.twoBankFrame_upper Q first_outward first_nonzero last_outward
        last_nonzero positive_phase common, equal]
    have phase := (R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
      positive_phase).injective same
    have real_part := congrArg Complex.re phase
    simp only [Complex.ofReal_re, Complex.mul_re, polarRay_re, Real.cos_pi_div_two,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at real_part
    have zero : r = 0 := NNReal.eq real_part
    rw [zero, R.radialPoint_zero]
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨R.start_mem, common ▸ Q.start_mem⟩

end Unfoldings.PolygonalRay
