module

public import Unfoldings.Geometry.MonotoneStripBoundedInjective

/-! Quantitative distance separation for continuous finite affine selections on whole strips. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- One common cone coefficient controls pairs on the whole slab. The bound does
not deteriorate with the number of pieces or the inset used to avoid its banks. -/
theorem lower_norm_bound_bounded_of_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c : ℝ}
    (nonnegative : 0 ≤ c)
    (bounds : ∀ i, ConeCoordinateBound (A i) c 1 ∧ ConeCoordinateBound (A i) c (-1))
    (a b : ℝ) {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F (S.boundedCarrier a b))
    (selection : ∀ z ∈ S.boundedCarrier a b, ∃ i, F z = A i z)
    {p q : ℂ} (first : p ∈ S.boundedCarrier a b) (last : q ∈ S.boundedCarrier a b) :
    c * ‖q - p‖ ≤ 2 * ‖F q - F p‖ := by
  have compare {p q : ℂ} (first : p ∈ S.boundedCarrier a b)
      (last : q ∈ S.boundedCarrier a b) (horizontal : p.re ≤ q.re) :
      c * ‖q - p‖ ≤ 2 * ‖F q - F p‖ := by
    have norm_input := Complex.norm_le_abs_re_add_abs_im (q - p)
    have re_output := (le_abs_self (F q - F p).re).trans (Complex.abs_re_le_norm _)
    have im_output := (le_abs_self (F q - F p).im).trans (Complex.abs_im_le_norm _)
    have neg_im_output := (neg_le_abs (F q - F p).im).trans (Complex.abs_im_le_norm _)
    simp only [Complex.sub_re, Complex.sub_im] at norm_input re_output im_output neg_im_output
    rcases le_total p.im q.im with vertical | vertical
    · have bound := finite_selection_bound_along_path_on (S.boundedCarrier a b)
        (fun i => A i) continuous Fcontinuous selection (fun i => (bounds i).1)
        (S.increasingPath first.1 last.1 horizontal vertical)
        (S.increasingPath_mem_bounded first last horizontal vertical)
        (S.increasingPath_re_mono first.1 last.1 horizontal vertical)
        (by simpa only [one_mul] using S.increasingPath_im_mono first.1 last.1 horizontal vertical)
      simp only [one_mul] at bound
      rw [abs_of_nonneg (sub_nonneg.mpr horizontal),
        abs_of_nonneg (sub_nonneg.mpr vertical)] at norm_input
      have norm_bound := mul_le_mul_of_nonneg_left norm_input nonnegative
      nlinarith
    · have bound := finite_selection_bound_along_path_on (S.boundedCarrier a b)
        (fun i => A i) continuous Fcontinuous selection (fun i => (bounds i).2)
        (Path.segment p q) (S.segmentPath_mem_bounded first last horizontal vertical)
        (segment_re_mono horizontal) (segment_neg_im_mono vertical)
      simp only [neg_mul, one_mul] at bound
      rw [abs_of_nonneg (sub_nonneg.mpr horizontal),
        abs_of_nonpos (sub_nonpos.mpr vertical)] at norm_input
      have norm_bound := mul_le_mul_of_nonneg_left norm_input nonnegative
      nlinarith
  rcases le_total p.re q.re with ordered | ordered
  · exact compare first last ordered
  · simpa only [norm_sub_rev] using compare last first ordered

/-- Strict axis tests give one positive lower coefficient for every pair on the slab. -/
theorem exists_lower_norm_bound_bounded_of_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j) (a b : ℝ)
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F (S.boundedCarrier a b))
    (selection : ∀ z ∈ S.boundedCarrier a b, ∃ i, F z = A i z) :
    ∃ c > 0, ∀ p ∈ S.boundedCarrier a b, ∀ q ∈ S.boundedCarrier a b,
      c * ‖q - p‖ ≤ 2 * ‖F q - F p‖ := by
  obtain ⟨c, positive, bounds⟩ := exists_common_affine_cone_bound A positive
  exact ⟨c, positive, fun _ first _ last => S.lower_norm_bound_bounded_of_affine_selection
    A continuous positive.le bounds a b Fcontinuous selection first last⟩

end Unfoldings.MonotoneStrip
