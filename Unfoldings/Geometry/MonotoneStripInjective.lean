module

public import Unfoldings.Geometry.MonotoneStripPaths
public import Unfoldings.Topology.IntervalLocalOrder

/-! Local quantitative cone bounds imply injectivity on a whole monotone strip. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- A local coordinate bound in the cone with increasing real coordinate and signed imaginary
coordinate. The same fixed coefficient is used at every point of the strip. -/
def LocalCoordinateBound (F : ℂ → ℂ) (c sign : ℝ) : Prop :=
  ∀ p ∈ S.carrier, ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧
    ∀ a ∈ S.carrier ∩ U, ∀ b ∈ S.carrier ∩ U,
      a.re ≤ b.re → sign * a.im ≤ sign * b.im →
        c * ((b.re + sign * b.im) - (a.re + sign * a.im)) ≤
          (F b).re + sign * (F b).im - ((F a).re + sign * (F a).im)

/-- An entire continuous monotone path inherits the local coordinate bound. -/
theorem coordinate_bound_along_path {F : ℂ → ℂ} {c sign : ℝ}
    (bound : S.LocalCoordinateBound F c sign) {p q : ℂ} (P : Path p q)
    (inside : ∀ t, P t ∈ S.carrier) (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => sign * (P t).im)) :
    c * ((q.re + sign * q.im) - (p.re + sign * p.im)) ≤
      (F q).re + sign * (F q).im - ((F p).re + sign * (F p).im) := by
  have total := interval_coordinate_bound_of_local
    (fun t => (P t).re + sign * (P t).im)
    (fun t => (F (P t)).re + sign * (F (P t)).im) c (fun t => ?_)
  · simpa only [Path.source, Path.target] using total
  · obtain ⟨U, opened, member, local_bound⟩ := bound (P t) (inside t)
    refine ⟨P ⁻¹' U, opened.preimage P.continuous, member, ?_⟩
    intro a first b last ordered
    exact local_bound (P a) ⟨inside a, first⟩ (P b) ⟨inside b, last⟩
      (horizontal ordered) (vertical ordered)

theorem segment_re_mono {p q : ℂ} (horizontal : p.re ≤ q.re) :
    Monotone (fun t => (Path.segment p q t).re) := by
  intro a b ordered
  have step : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr ordered
  have product := mul_nonneg step (sub_nonneg.mpr horizontal)
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module', Complex.add_re,
    Complex.smul_re, Complex.sub_re, smul_eq_mul]
  nlinarith

theorem segment_neg_im_mono {p q : ℂ} (vertical : q.im ≤ p.im) :
    Monotone (fun t => (-1 : ℝ) * (Path.segment p q t).im) := by
  intro a b ordered
  have step : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr ordered
  have product := mul_nonneg step (sub_nonneg.mpr vertical)
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module', Complex.add_im,
    Complex.smul_im, Complex.sub_im, smul_eq_mul]
  nlinarith

/-- Compare a pair whose real coordinates are already ordered, using either an increasing
connector or the straight mixed-coordinate segment. -/
theorem eq_of_image_eq_of_re_le {F : ℂ → ℂ} {c : ℝ} (positive : 0 < c)
    (forward : S.LocalCoordinateBound F c 1) (downward : S.LocalCoordinateBound F c (-1))
    {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier) (horizontal : p.re ≤ q.re)
    (same : F p = F q) : p = q := by
  rcases le_total p.im q.im with vertical | vertical
  · let P := S.increasingPath first last horizontal vertical
    have bound := S.coordinate_bound_along_path forward P
      (S.increasingPath_mem first last horizontal vertical)
      (S.increasingPath_re_mono first last horizontal vertical)
      (by simpa only [one_mul] using
        S.increasingPath_im_mono first last horizontal vertical)
    rw [same] at bound
    simp only [one_mul, sub_self] at bound
    have total : q.re + q.im ≤ p.re + p.im := by nlinarith
    exact Complex.ext (by linarith) (by linarith)
  · have bound := S.coordinate_bound_along_path downward (Path.segment p q)
      (S.segmentPath_mem first last horizontal vertical) (segment_re_mono horizontal)
      (segment_neg_im_mono vertical)
    rw [same] at bound
    simp only [neg_mul, one_mul, sub_self] at bound
    have total : q.re - q.im ≤ p.re - p.im := by nlinarith
    exact Complex.ext (by linarith) (by linarith)

/-- Local uniform cone bounds give global injectivity on a possibly nonconvex strip.
This is a geometric criterion; applications must derive the local bounds for their maps. -/
theorem injOn_of_local_coordinate_bounds {F : ℂ → ℂ} {c : ℝ} (positive : 0 < c)
    (forward : S.LocalCoordinateBound F c 1) (downward : S.LocalCoordinateBound F c (-1)) :
    Set.InjOn F S.carrier := by
  intro p first q last same
  rcases le_total p.re q.re with horizontal | horizontal
  · exact S.eq_of_image_eq_of_re_le positive forward downward first last horizontal same
  · exact (S.eq_of_image_eq_of_re_le positive forward downward last first horizontal same.symm).symm

end Unfoldings.MonotoneStrip
