module

public import Unfoldings.FewestNets.LatitudeStripSupport

/-! The endpoints of an actual row edge have equal support from its midpoint meridian. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

@[simp] theorem latitudeSite_north (longitude : ℝ) :
    latitudeSite 0 longitude = latitudeSite 0 0 := by
  unfold latitudeSite
  simp

@[simp] theorem latitudeSite_south (longitude : ℝ) :
    latitudeSite π longitude = latitudeSite π 0 := by
  unfold latitudeSite
  simp

theorem rowMidpoint_sub_rowLongitude {k : ℕ} (i : Fin k) :
    rowMidpoint k i - rowLongitude k i.val = π / (k : ℝ) := by
  unfold rowMidpoint rowLongitude
  ring

theorem rowLongitude_succ_sub_rowMidpoint {k : ℕ} (i : Fin k) :
    rowLongitude k (i.val + 1) - rowMidpoint k i = π / (k : ℝ) := by
  simp only [rowLongitude, rowMidpoint, Nat.cast_add, Nat.cast_one]
  ring

theorem rowMidpoint_closest_left {k : ℕ} (i : Fin k) :
    |rowMidpoint k i - rowLongitude k i.val| ≤ π / (k : ℝ) := by
  rw [rowMidpoint_sub_rowLongitude, abs_of_nonneg (by positivity)]

theorem latitudeRowSite_midpoint_support_eq (a : ℝ) (j : ℕ)
    (i : Fin (latitudeRowSize a j)) (ell : ℝ) :
    inner ℝ (latitudeSite ell (rowMidpoint (latitudeRowSize a j) i)) (latitudeRowSite a j i.val) =
      inner ℝ (latitudeSite ell (rowMidpoint (latitudeRowSize a j) i))
        (latitudeRowSite a j (i.val + 1)) := by
  let k := latitudeRowSize a j
  let longitude := rowMidpoint k i
  let h := π / (k : ℝ)
  have left : rowLongitude k i.val = longitude - h := by
    change rowLongitude k i.val = rowMidpoint k i - π / (k : ℝ)
    linarith only [rowMidpoint_sub_rowLongitude i]
  have right : rowLongitude k (i.val + 1) = longitude + h := by
    change rowLongitude k (i.val + 1) = rowMidpoint k i + π / (k : ℝ)
    linarith only [rowLongitude_succ_sub_rowMidpoint i]
  unfold latitudeRowSite
  rw [left, right]
  exact latitudeSymmetric_support_eq ell (latitudeColatitude a j) longitude h

end Unfoldings.FewestNets
