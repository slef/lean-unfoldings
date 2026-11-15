module

public import Unfoldings.Geometry.TwoBankGapSecondSector
public import Unfoldings.Geometry.PolygonalBankEdgeGerm
public import Unfoldings.Geometry.RadialRightCorner

/-! Actual straight finite bank pieces have whole intrinsic half-plane corner charts. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- A strict interior point of an original second-bank edge has angle exactly `pi`.
Other bank pieces, the occupied side and strict radial progress are all derived. -/
theorem exists_second_edge_point_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin m, Q.chain.vertex i.castSucc ≠ Q.chain.vertex i.succ)
    (i : Fin m) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    let p := Q.chain.point i t
    let frame := radialRightCornerFrame (p - Q.start) (Q.chain.edge i)
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
      (R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common ‖p - Q.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal δ),
      ∀ y, p + frame ((bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  dsimp only
  let p := Q.chain.point i t
  let r := ‖p - Q.start‖₊
  have radial : 0 < inner ℝ (p - Q.start) (Q.chain.edge i) :=
    Q.inner_edge_point_pos last_outward genuine i t bounds.1
  have actual : Q.radialPoint last_outward last_nonzero r = p :=
    Q.radialPoint_norm_eq_of_mem last_outward last_nonzero
      (Or.inl (Q.chain.point_mem_path_range i t))
  have radius : 0 < r := by
    change 0 < ‖p - Q.start‖
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Q.point_ne_start last_outward genuine i t bounds.1))
  have banks : Q.complexCarrierGerm (Q.radialPoint last_outward last_nonzero r) =
      radialRightCornerFrame (p - Q.start) (Q.chain.edge i) ''
        (Set.range (fun s : ℝ≥0 => (s : ℂ)) ∪
          Set.range (fun s : ℝ≥0 => (s : ℂ) * polarRay Real.pi)) := by
    rw [actual, Q.complexCarrierGerm_edge_point last_outward last_nonzero genuine i t bounds]
    simpa only [radialRightCornerWidth, radialLeftCornerWidth, add_sub_cancel_right] using
      radialRightCorner_bank_rays (p - Q.start) (Q.chain.edge i) (Q.chain.edge i) radial radial
  have normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior (radialRightCornerFrame (p - Q.start) (Q.chain.edge i) ''
        closedAngularSector Real.pi) := by
    rw [actual]
    simpa only [radialRightCornerWidth, radialLeftCornerWidth, add_sub_cancel_right] using
      radialRightCorner_normal_mem (p - Q.start) (Q.chain.edge i) (Q.chain.edge i) radial radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_second_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialRightCornerFrame (p - Q.start) (Q.chain.edge i)) Real.pi Real.pi_pos
    (by linarith [Real.pi_pos]) banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p] using! physical y

end Unfoldings.PolygonalRay
