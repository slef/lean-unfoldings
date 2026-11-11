module

public import Unfoldings.Geometry.AffineConeBounds
public import Unfoldings.Geometry.MonotoneStripSlab

/-! Finite calibrated face maps are injective on bounded-height monotone strips. -/

@[expose] public section

namespace Unfoldings

/-- The finite-selection estimate applies to a path in any domain, including a bounded strip. -/
theorem finite_selection_bound_along_path_on {ι : Type*} [Finite ι] (domain : Set ℂ)
    (branch : ι → ℂ → ℂ) (branch_continuous : ∀ i, Continuous (branch i))
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F domain)
    (selection : ∀ z ∈ domain, ∃ i, F z = branch i z) {c sign : ℝ}
    (branch_bound : ∀ i, MonotoneStrip.ConeCoordinateBound (branch i) c sign)
    {p q : ℂ} (P : Path p q) (inside : ∀ t, P t ∈ domain)
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => sign * (P t).im)) :
    c * ((q.re + sign * q.im) - (p.re + sign * p.im)) ≤
      (F q).re + sign * (F q).im - ((F p).re + sign * (F p).im) := by
  have Fpath : Continuous (fun t => F (P t)) :=
    Fcontinuous.comp_continuous P.continuous inside
  have total := finite_selection_coordinate_bound
    (fun t => (P t).re + sign * (P t).im)
    (fun t => (F (P t)).re + sign * (F (P t)).im)
    ((MonotoneStrip.continuous_signedHeight sign).comp P.continuous)
    ((MonotoneStrip.continuous_signedHeight sign).comp Fpath) c
    (fun i t => (branch i (P t)).re + sign * (branch i (P t)).im)
    (fun i => (MonotoneStrip.continuous_signedHeight sign).comp
      ((branch_continuous i).comp P.continuous))
    (fun i a b ordered => ?_) (fun t => ?_)
  · simpa only [Path.source, Path.target] using total
  · have bound := branch_bound i (P a) (P b) (horizontal ordered) (vertical ordered)
    dsimp only
    linarith
  · obtain ⟨i, equal⟩ := selection (P t) (inside t)
    exact ⟨i, congrArg (fun z : ℂ => z.re + sign * z.im) equal⟩

namespace MonotoneStrip

variable (S : MonotoneStrip)

/-- A finite facewise affine selection needs compatibility only on the bounded strip itself. -/
theorem injOn_bounded_of_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j) (a b : ℝ)
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F (S.boundedCarrier a b))
    (selection : ∀ z ∈ S.boundedCarrier a b, ∃ i, F z = A i z) :
    Set.InjOn F (S.boundedCarrier a b) := by
  obtain ⟨c, cpositive, bounds⟩ := exists_common_affine_cone_bound A positive
  have compare {p q : ℂ} (first : p ∈ S.boundedCarrier a b)
      (last : q ∈ S.boundedCarrier a b) (horizontal : p.re ≤ q.re)
      (same : F p = F q) : p = q := by
    rcases le_total p.im q.im with vertical | vertical
    · have bound := finite_selection_bound_along_path_on (S.boundedCarrier a b)
        (fun i => A i) continuous Fcontinuous selection (fun i => (bounds i).1)
        (S.increasingPath first.1 last.1 horizontal vertical)
        (S.increasingPath_mem_bounded first last horizontal vertical)
        (S.increasingPath_re_mono first.1 last.1 horizontal vertical)
        (by simpa only [one_mul] using
          S.increasingPath_im_mono first.1 last.1 horizontal vertical)
      rw [same] at bound
      simp only [one_mul, sub_self] at bound
      have total : q.re + q.im ≤ p.re + p.im := by nlinarith
      exact Complex.ext (by linarith) (by linarith)
    · have bound := finite_selection_bound_along_path_on (S.boundedCarrier a b)
        (fun i => A i) continuous Fcontinuous selection (fun i => (bounds i).2)
        (Path.segment p q) (S.segmentPath_mem_bounded first last horizontal vertical)
        (segment_re_mono horizontal) (segment_neg_im_mono vertical)
      rw [same] at bound
      simp only [neg_mul, one_mul, sub_self] at bound
      have total : q.re - q.im ≤ p.re - p.im := by nlinarith
      exact Complex.ext (by linarith) (by linarith)
  intro p first q last same
  rcases le_total p.re q.re with horizontal | horizontal
  · exact compare first last horizontal same
  · exact (compare last first horizontal same.symm).symm

end MonotoneStrip
end Unfoldings
