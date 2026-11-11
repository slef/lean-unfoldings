module

public import Unfoldings.Geometry.MonotoneStrip
public import Mathlib.Analysis.Convex.PathConnected

/-! Continuous paths inside monotone strips, with controlled signs in both coordinates. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

def pathHeight (p q : ℂ) (t : unitInterval) : ℝ :=
  (p.re + p.im) + (t : ℝ) * ((q.re + q.im) - (p.re + p.im))

theorem pathHeight_mono {p q : ℂ} (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) : Monotone (pathHeight p q) := by
  intro a b ordered
  have nonnegative : 0 ≤ (q.re + q.im) - (p.re + p.im) := by linarith
  have bound := mul_le_mul_of_nonneg_right
    (show (a : ℝ) ≤ (b : ℝ) from ordered) nonnegative
  change (p.re + p.im) + (a : ℝ) * _ ≤ (p.re + p.im) + (b : ℝ) * _
  linarith

/-- Coordinate-comparable endpoints admit an increasing path within the closed strip. -/
def increasingPath {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) : Path p q where
  toFun t := (S.connector p q).point (pathHeight p q t)
  continuous_toFun := (S.connector p q).point_continuous.comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))
  source' := by
    change (S.connector p q).point
      ((p.re + p.im) + (0 : ℝ) * ((q.re + q.im) - (p.re + p.im))) = p
    simpa only [zero_mul, add_zero] using S.connector_source first horizontal
  target' := by
    change (S.connector p q).point
      ((p.re + p.im) + (1 : ℝ) * ((q.re + q.im) - (p.re + p.im))) = q
    convert S.connector_target last vertical using 2
    ring

theorem increasingPath_mem {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) (t : unitInterval) :
    S.increasingPath first last horizontal vertical t ∈ S.carrier :=
  S.connector_mem p q (pathHeight p q t)

theorem increasingPath_re_mono {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) :
    Monotone (fun t => (S.increasingPath first last horizontal vertical t).re) :=
  (S.connector p q).coordinate_mono.comp (pathHeight_mono horizontal vertical)

theorem increasingPath_im_mono {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) :
    Monotone (fun t => (S.increasingPath first last horizontal vertical t).im) :=
  (S.connector p q).complement_mono.comp (pathHeight_mono horizontal vertical)

/-- If the endpoint coordinates are oppositely ordered, the entire straight path stays inside. -/
theorem segmentPath_mem {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : q.im ≤ p.im) (t : unitInterval) :
    Path.segment p q t ∈ S.carrier :=
  S.segment_subset_of_opposite_coordinates first last horizontal vertical
    (lineMap_mem_segment ℝ p q t.property)

end Unfoldings.MonotoneStrip
