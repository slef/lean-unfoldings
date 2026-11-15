module

public import Unfoldings.Geometry.TwoBankGapSecondSector
public import Unfoldings.Geometry.PolygonalBankTailInterior
public import Unfoldings.Geometry.RadialRightCorner

/-! Whole intrinsic half-plane charts along the actual unbounded second-bank tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- A positive point of the true entire second-bank tail has angle exactly `pi`.
Finite-edge degeneracies are allowed; tail isolation and strict radial progress are derived. -/
theorem exists_second_tail_point_chart (common : Q.start = R.start)
    (t : ℝ≥0) (positive : 0 < t) :
    let p := Q.tail t
    let frame := radialRightCornerFrame (p - Q.start) (Q.direction)
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
      (R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common ‖p - Q.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal δ),
      ∀ y, p + frame ((bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  dsimp only
  let p := Q.tail t
  let r := ‖p - Q.start‖₊
  have radial : 0 < inner ℝ (p - Q.start) (Q.direction) :=
    Q.inner_tail_point_pos last_outward last_nonzero t positive
  have actual : Q.radialPoint last_outward last_nonzero r = p :=
    Q.radialPoint_norm_eq_of_mem last_outward last_nonzero
      (Or.inr ⟨t, rfl⟩)
  have radius : 0 < r := by
    change 0 < ‖p - Q.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at radial
  have banks : Q.complexCarrierGerm (Q.radialPoint last_outward last_nonzero r) =
      radialRightCornerFrame (p - Q.start) (Q.direction) ''
        (Set.range (fun s : ℝ≥0 => (s : ℂ)) ∪
          Set.range (fun s : ℝ≥0 => (s : ℂ) * polarRay Real.pi)) := by
    rw [actual, Q.complexCarrierGerm_tail_point last_outward last_nonzero t positive]
    simpa only [radialRightCornerWidth, radialLeftCornerWidth, add_sub_cancel_right] using
      radialRightCorner_bank_rays (p - Q.start) (Q.direction) (Q.direction) radial radial
  have normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior (radialRightCornerFrame (p - Q.start) (Q.direction) ''
        closedAngularSector Real.pi) := by
    rw [actual]
    simpa only [radialRightCornerWidth, radialLeftCornerWidth, add_sub_cancel_right] using
      radialRightCorner_normal_mem (p - Q.start) (Q.direction) (Q.direction) radial radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_second_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialRightCornerFrame (p - Q.start) (Q.direction)) Real.pi Real.pi_pos
    (by linarith [Real.pi_pos]) banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p] using! physical y

end Unfoldings.PolygonalRay
