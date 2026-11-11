module

public import Unfoldings.Geometry.FiniteSelectionNormBounds
public import Unfoldings.Geometry.MonotoneStripBoundedInjective

/-! Continuous affine chart selections on bounded monotone strips have uniform Lipschitz bounds. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem lipschitzOnWith_bounded_of_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) (K : ℝ≥0)
    (linear_bound : ∀ i z, ‖(A i).linear z‖ ≤ K * ‖z‖) (a b : ℝ)
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F (S.boundedCarrier a b))
    (selection : ∀ z ∈ S.boundedCarrier a b, ∃ i, F z = A i z) :
    LipschitzOnWith (4 * K) F (S.boundedCarrier a b) := by
  have compare {p q : ℂ} (first : p ∈ S.boundedCarrier a b)
      (last : q ∈ S.boundedCarrier a b) (horizontal : p.re ≤ q.re) :
      ‖F q - F p‖ ≤ 2 * (K : ℝ) * (|q.re - p.re| + |q.im - p.im|) := by
    rcases le_total p.im q.im with vertical | vertical
    · let P := S.increasingPath first.1 last.1 horizontal vertical
      have inside := S.increasingPath_mem_bounded first last horizontal vertical
      have re := S.increasingPath_re_mono first.1 last.1 horizontal vertical
      have im := S.increasingPath_im_mono first.1 last.1 horizontal vertical
      have bound := finite_affine_selection_norm_bound_along_path A continuous K.coe_nonneg
        linear_bound P (fun t => (P t).re + (P t).im)
        ((Complex.continuous_re.comp P.continuous).add (Complex.continuous_im.comp P.continuous))
        (fun u v ordered => ?_) (Fcontinuous.comp_continuous P.continuous inside)
        (fun t => selection (P t) (inside t))
      · simp only [Path.source, Path.target] at bound
        rw [abs_of_nonneg (sub_nonneg.mpr horizontal), abs_of_nonneg (sub_nonneg.mpr vertical)]
        convert bound using 1
        ring
      · have estimate := Complex.norm_le_abs_re_add_abs_im (P v - P u)
        have real_order : (P u).re ≤ (P v).re := re ordered
        have imaginary_order : (P u).im ≤ (P v).im := im ordered
        simp only [Complex.sub_re, Complex.sub_im,
          abs_of_nonneg (sub_nonneg.mpr real_order),
          abs_of_nonneg (sub_nonneg.mpr imaginary_order)] at estimate
        linarith
    · let P := Path.segment p q
      have inside := S.segmentPath_mem_bounded first last horizontal vertical
      have re := segment_re_mono horizontal
      have im := segment_neg_im_mono vertical
      have bound := finite_affine_selection_norm_bound_along_path A continuous K.coe_nonneg
        linear_bound P (fun t => (P t).re - (P t).im)
        ((Complex.continuous_re.comp P.continuous).sub (Complex.continuous_im.comp P.continuous))
        (fun u v ordered => ?_) (Fcontinuous.comp_continuous P.continuous inside)
        (fun t => selection (P t) (inside t))
      · simp only [Path.source, Path.target] at bound
        rw [abs_of_nonneg (sub_nonneg.mpr horizontal), abs_of_nonpos (sub_nonpos.mpr vertical)]
        convert bound using 1
        ring
      · have estimate := Complex.norm_le_abs_re_add_abs_im (P v - P u)
        have decreasing : (P v).im ≤ (P u).im := by
          have order := im ordered
          simpa only [neg_mul, one_mul, neg_le_neg_iff] using order
        have real_order : (P u).re ≤ (P v).re := re ordered
        simp only [Complex.sub_re, Complex.sub_im, abs_of_nonneg (sub_nonneg.mpr real_order),
          abs_of_nonpos (sub_nonpos.mpr decreasing)] at estimate
        linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro p first q last
  have l1 : |q.re - p.re| + |q.im - p.im| ≤ 2 * ‖q - p‖ := by
    have re := Complex.abs_re_le_norm (q - p)
    have im := Complex.abs_im_le_norm (q - p)
    simp only [Complex.sub_re, Complex.sub_im] at re im
    linarith
  have bound : ‖F q - F p‖ ≤ 2 * (K : ℝ) * (|q.re - p.re| + |q.im - p.im|) := by
    rcases le_total p.re q.re with ordered | ordered
    · exact compare first last ordered
    · have swapped := compare last first ordered
      simpa only [norm_sub_rev, abs_sub_comm] using swapped
  have final_bound := bound.trans (mul_le_mul_of_nonneg_left l1 (by positivity))
  simp only [dist_eq_norm', NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith [final_bound]

end Unfoldings.MonotoneStrip
