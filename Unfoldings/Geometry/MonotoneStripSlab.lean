module

public import Unfoldings.Geometry.MonotoneStripPaths

/-! The bounded-height portions of monotone strips retain their connecting paths. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

def boundedCarrier (a b : ℝ) : Set ℂ :=
  {z | z ∈ S.carrier ∧ z.re + z.im ∈ Set.Icc a b}

theorem boundedCarrier_subset (a b : ℝ) : S.boundedCarrier a b ⊆ S.carrier :=
  fun _ member => member.1

theorem increasingPath_height {p q : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) (t : unitInterval) :
    (S.increasingPath first last horizontal vertical t).re +
      (S.increasingPath first last horizontal vertical t).im = pathHeight p q t :=
  (S.connector p q).point_height _

/-- The constructed increasing connector never leaves the height interval of its endpoints. -/
theorem increasingPath_mem_bounded {a b : ℝ} {p q : ℂ}
    (first : p ∈ S.boundedCarrier a b) (last : q ∈ S.boundedCarrier a b)
    (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im) (t : unitInterval) :
    S.increasingPath first.1 last.1 horizontal vertical t ∈ S.boundedCarrier a b := by
  refine ⟨S.increasingPath_mem first.1 last.1 horizontal vertical t, ?_⟩
  rw [S.increasingPath_height]
  have blend := (convex_Icc a b).segment_subset first.2 last.2
    (lineMap_mem_segment ℝ (p.re + p.im) (q.re + q.im) t.property)
  have equal : pathHeight p q t =
      AffineMap.lineMap (p.re + p.im) (q.re + q.im) (t : ℝ) := by
    simp only [pathHeight, AffineMap.lineMap_apply_module', smul_eq_mul]
    ring
  rw [equal]
  exact blend

/-- Mixed-coordinate straight segments also remain in the bounded-height strip. -/
theorem segmentPath_mem_bounded {a b : ℝ} {p q : ℂ}
    (first : p ∈ S.boundedCarrier a b) (last : q ∈ S.boundedCarrier a b)
    (horizontal : p.re ≤ q.re) (vertical : q.im ≤ p.im) (t : unitInterval) :
    Path.segment p q t ∈ S.boundedCarrier a b := by
  refine ⟨S.segmentPath_mem first.1 last.1 horizontal vertical t, ?_⟩
  have equal : (Path.segment p q t).re + (Path.segment p q t).im =
      AffineMap.lineMap (p.re + p.im) (q.re + q.im) (t : ℝ) := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module', Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    ring
  rw [equal]
  exact (convex_Icc a b).segment_subset first.2 last.2
    (lineMap_mem_segment ℝ (p.re + p.im) (q.re + q.im) t.property)

end Unfoldings.MonotoneStrip
