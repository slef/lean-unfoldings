module

public import Unfoldings.Geometry.FiveSectors
public import Unfoldings.Geometry.WedgeRotationFrame

/-! Five numerical quadrant frames cover the whole roof, with one common positive margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def fiveSectorFrame (t : ℝ) (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    AcuteWedgeFrame (fiveSectorFirst t i) (fiveSectorLast t i) := by
  cases i with
  | inl i => exact threeSectorFrame t positive small i
  | inr upper =>
    exact Classical.choice (exists_acuteWedgeFrame _ _
      (fiveSector_banks_orient_pos positive small (Sum.inr upper)).ne'
      (fiveSector_width_lt_pi_div_two positive small (Sum.inr upper)))

def fiveSectorMargin (t : ℝ) (positive : 0 < t) (small : t < 1) : ℝ :=
  min (threeSectorMargin t positive small)
    (min (fiveSectorFrame t positive small (Sum.inr false)).margin
      (fiveSectorFrame t positive small (Sum.inr true)).margin)

theorem fiveSectorMargin_pos (t : ℝ) (positive : 0 < t) (small : t < 1) :
    0 < fiveSectorMargin t positive small :=
  lt_min (threeSectorMargin_pos t positive small)
    (lt_min (fiveSectorFrame t positive small (Sum.inr false)).positive
      (fiveSectorFrame t positive small (Sum.inr true)).positive)

theorem fiveSectorMargin_le (t : ℝ) (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    fiveSectorMargin t positive small ≤ (fiveSectorFrame t positive small i).margin := by
  cases i with
  | inl i => exact (min_le_left _ _).trans (threeSectorMargin_le t positive small i)
  | inr upper =>
    cases upper
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The extra forward sectors have the same robust common-quadrant guarantee as the old three. -/
theorem fiveSector_quadrant_of_angle_close (t : ℝ) (positive : 0 < t) (small : t < 1)
    (i : FiveSector) {x : Plane} (inside : x ∈ closedFiveSector t i) (nonzero : x ≠ 0)
    {y : ℂ} (close : InnerProductGeometry.angle y
      (Complex.orthonormalBasisOneI.repr.symm x) < fiveSectorMargin t positive small) :
    0 < ((Complex.orthonormalBasisOneI.repr.trans
      (fiveSectorFrame t positive small i).place) y).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (fiveSectorFrame t positive small i).place) y).im :=
  (fiveSectorFrame t positive small i).quadrant_of_projected_angle_close inside nonzero
    (close.trans_le (fiveSectorMargin_le t positive small i))

/-- Every sector frame preserves the sign of actual complex bank-opening rotations. -/
theorem fiveSectorFrame_commutes_mul (t : ℝ) (positive : 0 < t) (small : t < 1)
    (i : FiveSector) (z w : ℂ) :
    (Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place) (z * w) =
      z * (Complex.orthonormalBasisOneI.repr.trans (fiveSectorFrame t positive small i).place) w :=
  (fiveSectorFrame t positive small i).complex_frame_commutes_mul
    (fiveSector_banks_orient_pos positive small i) z w

end Unfoldings
