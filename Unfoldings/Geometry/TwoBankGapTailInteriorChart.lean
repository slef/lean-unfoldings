module

public import Unfoldings.Geometry.TwoBankGapBankSector
public import Unfoldings.Geometry.PolygonalBankTailInterior
public import Unfoldings.Geometry.RadialCornerSector

/-! Whole intrinsic half-plane charts along the actual unbounded first-bank tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- A positive point of the true entire first-bank tail has angle exactly `pi`.
Finite-edge degeneracies are allowed; tail isolation and strict radial progress are derived. -/
theorem exists_first_tail_point_chart (common : Q.start = R.start)
    (t : ℝ≥0) (positive : 0 < t) :
    let p := R.tail t
    let frame := radialLeftCornerFrame (p - R.start) (R.direction)
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
      (R.twoBankFirstBankPoint Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common ‖p - R.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal δ),
      ∀ y, p + frame ((bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  dsimp only
  let p := R.tail t
  let r := ‖p - R.start‖₊
  have radial : 0 < inner ℝ (p - R.start) (R.direction) :=
    R.inner_tail_point_pos first_outward first_nonzero t positive
  have actual : R.radialPoint first_outward first_nonzero r = p :=
    R.radialPoint_norm_eq_of_mem first_outward first_nonzero
      (Or.inr ⟨t, rfl⟩)
  have radius : 0 < r := by
    change 0 < ‖p - R.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at radial
  have banks : R.complexCarrierGerm (R.radialPoint first_outward first_nonzero r) =
      radialLeftCornerFrame (p - R.start) (R.direction) ''
        (Set.range (fun s : ℝ≥0 => (s : ℂ)) ∪
          Set.range (fun s : ℝ≥0 => (s : ℂ) * polarRay Real.pi)) := by
    rw [actual, R.complexCarrierGerm_tail_point first_outward first_nonzero t positive]
    simpa only [radialLeftCornerWidth, add_sub_cancel_right] using
      radialLeftCorner_bank_rays (p - R.start) (R.direction) (R.direction) radial radial
  have normal : Complex.I * (R.radialPoint first_outward first_nonzero r - R.start) ∈
      interior (radialLeftCornerFrame (p - R.start) (R.direction) ''
        closedAngularSector Real.pi) := by
    rw [actual]
    simpa only [radialLeftCornerWidth, add_sub_cancel_right] using
      radialLeftCorner_normal_mem (p - R.start) (R.direction) (R.direction) radial radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_first_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialLeftCornerFrame (p - R.start) (R.direction)) Real.pi Real.pi_pos
    (by linarith [Real.pi_pos]) banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p] using! physical y

end Unfoldings.PolygonalRay
