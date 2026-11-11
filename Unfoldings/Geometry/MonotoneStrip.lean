module

public import Unfoldings.Geometry.MonotoneHeightGraph
public import Mathlib.Topology.Path
public import Mathlib.Analysis.Convex.Segment

/-! Closed strips between coordinate-monotone boundaries have monotone connecting paths. -/

@[expose] public section

namespace Unfoldings

namespace MonotoneHeightGraph

/-- A vertical line in the plane, parametrized by diagonal height. -/
def constant (x : ℝ) : MonotoneHeightGraph where
  coordinate _ := x
  coordinate_mono _ _ _ := le_rfl
  complement_mono _ _ ordered := sub_le_sub_right ordered x

/-- A horizontal line in the plane, parametrized by diagonal height. -/
def horizontal (y : ℝ) : MonotoneHeightGraph where
  coordinate h := h - y
  coordinate_mono _ _ ordered := sub_le_sub_right ordered y
  complement_mono := by
    intro a b _
    simp only [sub_sub_cancel]
    exact le_rfl

/-- First move horizontally from `p`, then vertically toward `q`.
The lattice description gives a graph on all real heights, with no division. -/
def elbow (p q : ℂ) : MonotoneHeightGraph :=
  (constant q.re).min ((constant p.re).max (horizontal p.im))

theorem elbow_source {p q : ℂ} (ordered : p.re ≤ q.re) :
    (elbow p q).coordinate (p.re + p.im) = p.re := by
  change Min.min q.re (Max.max p.re (p.re + p.im - p.im)) = p.re
  rw [add_sub_cancel_right, max_self, min_eq_right ordered]

theorem elbow_target {p q : ℂ} (ordered : p.im ≤ q.im) :
    (elbow p q).coordinate (q.re + q.im) = q.re := by
  change Min.min q.re (Max.max p.re (q.re + q.im - p.im)) = q.re
  exact min_eq_left ((show q.re ≤ q.re + q.im - p.im by linarith).trans (le_max_right _ _))

end MonotoneHeightGraph

/-- The region between two monotone graphs, including boundary contacts and zero-width tails. -/
structure MonotoneStrip where
  lower : MonotoneHeightGraph
  upper : MonotoneHeightGraph
  ordered : ∀ h, lower.coordinate h ≤ upper.coordinate h

namespace MonotoneStrip

variable (S : MonotoneStrip)

def carrier : Set ℂ :=
  {z | S.lower.coordinate (z.re + z.im) ≤ z.re ∧
    z.re ≤ S.upper.coordinate (z.re + z.im)}

/-- Clamping gives a connector inside the strip, with the required endpoints. -/
def connector (p q : ℂ) : MonotoneHeightGraph :=
  S.lower.clamp S.upper (MonotoneHeightGraph.elbow p q)

theorem connector_mem (p q : ℂ) (h : ℝ) : (S.connector p q).point h ∈ S.carrier := by
  change S.lower.coordinate (((S.connector p q).point h).re +
    ((S.connector p q).point h).im) ≤ _ ∧ _
  rw [(S.connector p q).point_height]
  exact S.lower.clamp_mem S.upper _ S.ordered h

theorem connector_source {p q : ℂ} (member : p ∈ S.carrier) (ordered : p.re ≤ q.re) :
    (S.connector p q).point (p.re + p.im) = p := by
  have elbow := MonotoneHeightGraph.elbow_source ordered
  have equal : (S.connector p q).coordinate (p.re + p.im) = p.re := by
    have bounds : S.lower.coordinate (p.re + p.im) ≤
        (MonotoneHeightGraph.elbow p q).coordinate (p.re + p.im) ∧
        (MonotoneHeightGraph.elbow p q).coordinate (p.re + p.im) ≤
          S.upper.coordinate (p.re + p.im) := by
      rw [elbow]
      exact member
    exact (S.lower.clamp_eq S.upper _ bounds.1 bounds.2).trans elbow
  apply Complex.ext
  · exact equal
  · change p.re + p.im - _ = p.im
    rw [equal]
    ring

theorem connector_target {p q : ℂ} (member : q ∈ S.carrier) (ordered : p.im ≤ q.im) :
    (S.connector p q).point (q.re + q.im) = q := by
  have elbow := MonotoneHeightGraph.elbow_target ordered
  have equal : (S.connector p q).coordinate (q.re + q.im) = q.re := by
    have bounds : S.lower.coordinate (q.re + q.im) ≤
        (MonotoneHeightGraph.elbow p q).coordinate (q.re + q.im) ∧
        (MonotoneHeightGraph.elbow p q).coordinate (q.re + q.im) ≤
          S.upper.coordinate (q.re + q.im) := by
      rw [elbow]
      exact member
    exact (S.lower.clamp_eq S.upper _ bounds.1 bounds.2).trans elbow
  apply Complex.ext
  · exact equal
  · change q.re + q.im - _ = q.im
    rw [equal]
    ring

/-- Mixed coordinate rectangles lie in the strip, even though the strip need not be convex. -/
theorem rectangle_mem {p q z : ℂ} (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (left : p.re ≤ z.re) (right : z.re ≤ q.re)
    (bottom : q.im ≤ z.im) (top : z.im ≤ p.im) : z ∈ S.carrier := by
  constructor
  · rcases le_total (z.re + z.im) (p.re + p.im) with before | after
    · exact (S.lower.coordinate_mono before).trans (first.1.trans left)
    · have bound := S.lower.complement_mono after
      linarith [first.1]
  · rcases le_total (z.re + z.im) (q.re + q.im) with before | after
    · have bound := S.upper.complement_mono before
      linarith [last.2]
    · exact right.trans (last.2.trans (S.upper.coordinate_mono after))

/-- Oppositely ordered coordinate endpoints can be joined by the straight segment. -/
theorem segment_subset_of_opposite_coordinates {p q : ℂ}
    (first : p ∈ S.carrier) (last : q ∈ S.carrier)
    (horizontal : p.re ≤ q.re) (vertical : q.im ≤ p.im) :
    segment ℝ p q ⊆ S.carrier := by
  rintro z ⟨a, b, anonnegative, bnonnegative, sum, rfl⟩
  have px := congrArg (fun r => r * p.re) sum
  have qx := congrArg (fun r => r * q.re) sum
  have py := congrArg (fun r => r * p.im) sum
  have qy := congrArg (fun r => r * q.im) sum
  simp only [add_mul, one_mul] at px qx py qy
  apply S.rectangle_mem first last
  all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  · nlinarith [mul_nonneg bnonnegative (sub_nonneg.mpr horizontal)]
  · nlinarith [mul_nonneg anonnegative (sub_nonneg.mpr horizontal)]
  · nlinarith [mul_nonneg anonnegative (sub_nonneg.mpr vertical)]
  · nlinarith [mul_nonneg bnonnegative (sub_nonneg.mpr vertical)]

end MonotoneStrip
end Unfoldings
