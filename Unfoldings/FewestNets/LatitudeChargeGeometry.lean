module

public import Unfoldings.FewestNets.LatitudeTriangleInterval
public import Unfoldings.FewestNets.CheckedLatitudeSweep

/-! The interval inputs describe the actual spherical triangles in the latitude sweep. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real LatitudeRings

/-- The exact offset of a numbered apex from the midpoint of a base edge. -/
def sweepOffset (m n i k : ℕ) : ℝ :=
  π * ((2 * (k : ℝ) * m - (2 * (i : ℝ) + 1) * n) / ((m : ℝ) * n))

private theorem base_left_longitude {m : ℕ} (i : Fin m) :
    rowMidpoint m i - π / m = rowLongitude m i := by
  unfold rowMidpoint rowLongitude
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  field_simp [hm]
  <;> ring

private theorem base_right_longitude {m : ℕ} (i : Fin m) :
    rowMidpoint m i + π / m = rowLongitude m (i.val + 1) := by
  unfold rowMidpoint rowLongitude
  push_cast
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  field_simp [hm]
  <;> ring

private theorem apex_longitude {m n : ℕ} (i : Fin m) (n0 : n ≠ 0) (k : ℕ) :
    rowMidpoint m i + sweepOffset m n i k = rowLongitude n k := by
  unfold rowMidpoint sweepOffset rowLongitude
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n0
  field_simp [hm, hn]
  <;> ring

/-- The three points are written in symmetric base coordinates. -/
def latitudeTriangleVertices (b c lon h t : ℝ) (reversed : Bool) : Fin 3 → Space :=
  let l := latitudeSite b (lon - h)
  let r := latitudeSite b (lon + h)
  let p := latitudeSite c (lon + t)
  if reversed then ![r, l, p] else ![l, r, p]

theorem latitudeTriangleVertices_chord (b c lon h t : ℝ) (reversed : Bool) (j : Fin 3) :
    ‖latitudeTriangleVertices b c lon h t reversed j -
      latitudeTriangleVertices b c lon h t reversed (j + 1)‖ ^ 2 =
      latitudeChordSquares b c (c - b) h t reversed j := by
  have base : ‖latitudeSite b (lon - h) - latitudeSite b (lon + h)‖ ^ 2 =
      4 * (sin b * sin h) ^ 2 := by
    rw [latitudeSite_chord_sq, sub_self, zero_div, sin_zero,
      show (lon + h - (lon - h)) / 2 = h by ring]
    ring
  have right : ‖latitudeSite b (lon + h) - latitudeSite c (lon + t)‖ ^ 2 =
      4 * sin ((c - b) / 2) ^ 2 + 4 * sin b * sin c * sin ((t - h) / 2) ^ 2 := by
    rw [latitudeSite_chord_sq, show lon + t - (lon + h) = t - h by ring]
  have left : ‖latitudeSite b (lon - h) - latitudeSite c (lon + t)‖ ^ 2 =
      4 * sin ((c - b) / 2) ^ 2 + 4 * sin b * sin c * sin ((t + h) / 2) ^ 2 := by
    rw [latitudeSite_chord_sq, show lon + t - (lon - h) = t + h by ring]
  cases reversed <;> fin_cases j
  · exact base
  · exact right
  · rw [norm_sub_rev]
    exact left
  · rw [norm_sub_rev]
    exact base
  · exact left
  · rw [norm_sub_rev]
    exact right

theorem latitudeTriangleVertices_absDet (b c lon h t : ℝ) (reversed : Bool) :
    |spatialRayDet (latitudeTriangleVertices b c lon h t reversed 0)
      (latitudeTriangleVertices b c lon h t reversed 1)
      (latitudeTriangleVertices b c lon h t reversed 2)| = |latitudeDetValue b c (c - b) h t| := by
  have det := latitudeSite_det_of_base b c lon h t
  rw [show b - c = -(c - b) by ring, sin_neg] at det
  cases reversed
  · exact congrArg abs det
  · change |spatialRayDet (latitudeSite b (lon + h)) (latitudeSite b (lon - h))
        (latitudeSite c (lon + t))| = _
    rw [show spatialRayDet (latitudeSite b (lon + h)) (latitudeSite b (lon - h)) (latitudeSite c (lon + t)) =
          -spatialRayDet (latitudeSite b (lon - h)) (latitudeSite b (lon + h)) (latitudeSite c (lon + t)) by
        unfold spatialRayDet
        ring, abs_neg]
    exact congrArg abs det

def sweepTriangleCharge (lo hi step : ℝ) {m n : ℕ} (edge : Fin m ⊕ Fin n) : ℝ :=
  match edge with
  | .inl i => latitudeTriangleCharge lo hi step (π / m) (sweepOffset m n i (oppositeIndex edge)) false
  | .inr i => latitudeTriangleCharge hi lo (-step) (π / n) (sweepOffset n m i (oppositeIndex edge)) true

private theorem charge_of_vertices {a b c lon h t : ℝ} (i : AnnularTriangle a) (rev : Bool)
    (vertices : (rings a).annularVertices i = latitudeTriangleVertices b c lon h t rev) :
    annularAlgebraicCharge i = latitudeTriangleCharge b c (c - b) h t rev := by
  have sides (j : Fin 3) : annularSineSquared i j = latitudeSineSquares b c (c - b) h t rev j := by
    rw [annularSineSquared, annularSideLength,
      sphericalSide_sin_sq_eq_chord _ _ ((rings a).annularVertices_unit i j)
        ((rings a).annularVertices_unit i (j + 1)), vertices, latitudeSineSquares, max_eq_right (by
          rw [← latitudeTriangleVertices_chord b c lon h t rev j]
          positivity), latitudeTriangleVertices_chord]
  have det : annularAbsDet i = |latitudeDetValue b c (c - b) h t| := by
    rw [annularAbsDet, vertices, latitudeTriangleVertices_absDet]
  simp only [annularAlgebraicCharge, annularMaxSineSquared, sides, det, latitudeTriangleCharge]

/-- Charge correspondence for each actual advancing midpoint, including the seam. -/
theorem annularAlgebraicCharge_eq_sweep {a : ℝ} (i : AnnularTriangle a)
    (m0 : rowSize a i.1.val ≠ 0) (n0 : rowSize a (i.1.val + 1) ≠ 0) :
    annularAlgebraicCharge i =
      sweepTriangleCharge (colatitude a i.1.val) (colatitude a (i.1.val + 1))
        (colatitude a (i.1.val + 1) - colatitude a i.1.val)
        (sweepOrder _ _ i.2) := by
  let G := rings a
  let j := i.1.val
  let m := rowSize a j
  let n := rowSize a (j + 1)
  let pass := sweepOrder m n
  change _ = sweepTriangleCharge _ _ _ (pass i.2)
  cases edge : pass i.2 with
  | inl b =>
    rw [sweepTriangleCharge]
    apply charge_of_vertices (lon := rowMidpoint m b)
    have apex := oppositeIndex_inl_eq pass (sweepOrder_sorted m n) i.2 b edge
    unfold LatitudeRings.annularVertices
    change latitudeSweepChordVertices G j pass i.2 = _
    rw [latitudeSweepChordVertices, edge]
    unfold latitudeTriangleVertices
    rw [if_neg Bool.false_ne_true, base_left_longitude, base_right_longitude, apex_longitude b n0]
    simp only [latitudeSweepCrossSites, rowSite, Fin.val_castSucc, apex]
    rfl
  | inr b =>
    rw [sweepTriangleCharge, neg_sub]
    apply charge_of_vertices (lon := rowMidpoint n b)
    have apex := oppositeIndex_inr_eq pass (sweepOrder_sorted m n) i.2 b edge
    unfold LatitudeRings.annularVertices
    change latitudeSweepChordVertices G j pass i.2 = _
    rw [latitudeSweepChordVertices, edge]
    unfold latitudeTriangleVertices
    rw [if_pos rfl, base_left_longitude, base_right_longitude, apex_longitude b m0]
    simp only [latitudeSweepCrossSites, rowSite, Fin.val_castSucc, apex]
    rfl

end Unfoldings.FewestNets.RevisedLatitudeGrid
