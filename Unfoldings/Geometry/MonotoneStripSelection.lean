module

public import Unfoldings.Geometry.MonotoneStripInjective
public import Unfoldings.Topology.FiniteMonotoneSelection

/-! Injectivity of continuous finite facewise selections on monotone strips. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- A quantitative coordinate bound for a whole map on one signed coordinate cone. -/
def ConeCoordinateBound (F : ℂ → ℂ) (c sign : ℝ) : Prop :=
  ∀ a b : ℂ, a.re ≤ b.re → sign * a.im ≤ sign * b.im →
    c * ((b.re + sign * b.im) - (a.re + sign * a.im)) ≤
      (F b).re + sign * (F b).im - ((F a).re + sign * (F a).im)

omit S in
theorem continuous_signedHeight (sign : ℝ) : Continuous (fun z : ℂ => z.re + sign * z.im) :=
  Complex.continuous_re.add (continuous_const.mul Complex.continuous_im)

/-- Genuine face maps may switch infinitely often along a continuous connector. Their common
cone estimate still controls the selected map between the connector endpoints. -/
theorem finite_selection_bound_along_path {ι : Type*} [Finite ι]
    (branch : ι → ℂ → ℂ) (branch_continuous : ∀ i, Continuous (branch i))
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F S.carrier)
    (selection : ∀ z ∈ S.carrier, ∃ i, F z = branch i z) {c sign : ℝ}
    (branch_bound : ∀ i, ConeCoordinateBound (branch i) c sign)
    {p q : ℂ} (P : Path p q) (inside : ∀ t, P t ∈ S.carrier)
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => sign * (P t).im)) :
    c * ((q.re + sign * q.im) - (p.re + sign * p.im)) ≤
      (F q).re + sign * (F q).im - ((F p).re + sign * (F p).im) := by
  have Fpath : Continuous (fun t => F (P t)) :=
    Fcontinuous.comp_continuous P.continuous inside
  have total := finite_selection_coordinate_bound
    (fun t => (P t).re + sign * (P t).im)
    (fun t => (F (P t)).re + sign * (F (P t)).im)
    ((continuous_signedHeight sign).comp P.continuous)
    ((continuous_signedHeight sign).comp Fpath) c
    (fun i t => (branch i (P t)).re + sign * (branch i (P t)).im)
    (fun i => (continuous_signedHeight sign).comp ((branch_continuous i).comp P.continuous))
    (fun i a b ordered => ?_) (fun t => ?_)
  · simpa only [Path.source, Path.target] using total
  · have bound := branch_bound i (P a) (P b) (horizontal ordered) (vertical ordered)
    dsimp only
    linarith
  · obtain ⟨i, equal⟩ := selection (P t) (inside t)
    exact ⟨i, congrArg (fun z : ℂ => z.re + sign * z.im) equal⟩

/-- A continuous map assembled from finitely many cone-controlled face maps is injective on
the strip. All branch compatibility is contained in continuity of the actual assembled map. -/
theorem injOn_of_finite_selection {ι : Type*} [Finite ι]
    (branch : ι → ℂ → ℂ) (branch_continuous : ∀ i, Continuous (branch i))
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F S.carrier)
    (selection : ∀ z ∈ S.carrier, ∃ i, F z = branch i z) {c : ℝ} (positive : 0 < c)
    (forward : ∀ i, ConeCoordinateBound (branch i) c 1)
    (downward : ∀ i, ConeCoordinateBound (branch i) c (-1)) : Set.InjOn F S.carrier := by
  apply S.injOn_of_local_coordinate_bounds positive
  · intro z member
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
    intro p first q last horizontal vertical
    have increasing : p.im ≤ q.im := by simpa only [one_mul] using vertical
    exact S.finite_selection_bound_along_path branch branch_continuous Fcontinuous selection
      forward (S.increasingPath first.1 last.1 horizontal increasing)
      (S.increasingPath_mem first.1 last.1 horizontal increasing)
      (S.increasingPath_re_mono first.1 last.1 horizontal increasing)
      (by simpa only [one_mul] using
        S.increasingPath_im_mono first.1 last.1 horizontal increasing)
  · intro z member
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
    intro p first q last horizontal vertical
    have decreasing : q.im ≤ p.im := by linarith
    exact S.finite_selection_bound_along_path branch branch_continuous Fcontinuous selection
      downward (Path.segment p q) (S.segmentPath_mem first.1 last.1 horizontal decreasing)
      (segment_re_mono horizontal) (segment_neg_im_mono decreasing)

end Unfoldings.MonotoneStrip
