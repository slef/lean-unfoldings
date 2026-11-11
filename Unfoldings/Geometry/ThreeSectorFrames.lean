module

public import Unfoldings.Geometry.RobustQuadrant
public import Unfoldings.Geometry.ThreeSectorRays

/-! Three numerical acute-wedge frames and one positive shared perturbation margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem threeSector_banks_orient_pos {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : Fin 3) : 0 < orient 0 (threeSectorRay t i.castSucc) (threeSectorRay t i.succ) := by
  have determinant := threeSectorDet_pos positive.le small i
  have identity : orient 0 (threeSectorRay t i.castSucc) (threeSectorRay t i.succ) =
      threeSectorDet t i := by
    fin_cases i <;> norm_num [threeSectorRay, threeSectorDet, orient] <;> ring
  rwa [identity]

/-- These three frames depend only on the already fixed numerical sector parameter. -/
def threeSectorFrame (t : ℝ) (positive : 0 < t) (small : t < 1) (i : Fin 3) :
    AcuteWedgeFrame (threeSectorRay t i.castSucc) (threeSectorRay t i.succ) :=
  Classical.choice (exists_acuteWedgeFrame _ _ (threeSector_banks_orient_pos positive small i).ne'
    (threeSectorWidth_lt_pi_div_two positive small i))

/-- One positive numerical angular tolerance works on all three fixed sector frames. -/
def threeSectorMargin (t : ℝ) (positive : 0 < t) (small : t < 1) : ℝ :=
  min (threeSectorFrame t positive small 0).margin
    (min (threeSectorFrame t positive small 1).margin (threeSectorFrame t positive small 2).margin)

theorem threeSectorMargin_pos (t : ℝ) (positive : 0 < t) (small : t < 1) :
    0 < threeSectorMargin t positive small :=
  lt_min (threeSectorFrame t positive small 0).positive
    (lt_min (threeSectorFrame t positive small 1).positive
      (threeSectorFrame t positive small 2).positive)

theorem threeSectorMargin_le (t : ℝ) (positive : 0 < t) (small : t < 1) (i : Fin 3) :
    threeSectorMargin t positive small ≤ (threeSectorFrame t positive small i).margin := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- A direction close to any closed original sector lies in that sector's fixed open quadrant. -/
theorem threeSector_quadrant_of_angle_close (t : ℝ) (positive : 0 < t) (small : t < 1)
    (i : Fin 3) {x : Plane} (inside : x ∈ closedThreeSector t i) (nonzero : x ≠ 0)
    {y : ℂ} (close : InnerProductGeometry.angle y
      (Complex.orthonormalBasisOneI.repr.symm x) < threeSectorMargin t positive small) :
    0 < ((Complex.orthonormalBasisOneI.repr.trans
      (threeSectorFrame t positive small i).place) y).re ∧
    0 < ((Complex.orthonormalBasisOneI.repr.trans
      (threeSectorFrame t positive small i).place) y).im :=
  (threeSectorFrame t positive small i).quadrant_of_projected_angle_close
    (inDirectionWedge_of_closedThreeSector positive.le small i inside) nonzero
    (close.trans_le (threeSectorMargin_le t positive small i))

end Unfoldings
