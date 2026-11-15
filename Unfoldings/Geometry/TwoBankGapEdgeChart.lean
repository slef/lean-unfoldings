module

public import Unfoldings.Geometry.TwoBankGapBankSector
public import Unfoldings.Geometry.PolygonalBankEdgeGerm
public import Unfoldings.Geometry.RadialCornerSector

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

/-- A strict interior point of an original first-bank edge has angle exactly `pi`.
Other bank pieces, the occupied side and strict radial progress are all derived. -/
theorem exists_first_edge_point_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    let p := R.chain.point i t
    let frame := radialLeftCornerFrame (p - R.start) (R.chain.edge i)
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
      (R.twoBankFirstBankPoint Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common ‖p - R.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal δ),
      ∀ y, p + frame ((bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  dsimp only
  let p := R.chain.point i t
  let r := ‖p - R.start‖₊
  have radial : 0 < inner ℝ (p - R.start) (R.chain.edge i) :=
    R.inner_edge_point_pos first_outward genuine i t bounds.1
  have actual : R.radialPoint first_outward first_nonzero r = p :=
    R.radialPoint_norm_eq_of_mem first_outward first_nonzero
      (Or.inl (R.chain.point_mem_path_range i t))
  have radius : 0 < r := by
    change 0 < ‖p - R.start‖
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (R.point_ne_start first_outward genuine i t bounds.1))
  have banks : R.complexCarrierGerm (R.radialPoint first_outward first_nonzero r) =
      radialLeftCornerFrame (p - R.start) (R.chain.edge i) ''
        (Set.range (fun s : ℝ≥0 => (s : ℂ)) ∪
          Set.range (fun s : ℝ≥0 => (s : ℂ) * polarRay Real.pi)) := by
    rw [actual, R.complexCarrierGerm_edge_point first_outward first_nonzero genuine i t bounds]
    simpa only [radialLeftCornerWidth, add_sub_cancel_right] using
      radialLeftCorner_bank_rays (p - R.start) (R.chain.edge i) (R.chain.edge i) radial radial
  have normal : Complex.I * (R.radialPoint first_outward first_nonzero r - R.start) ∈
      interior (radialLeftCornerFrame (p - R.start) (R.chain.edge i) ''
        closedAngularSector Real.pi) := by
    rw [actual]
    simpa only [radialLeftCornerWidth, add_sub_cancel_right] using
      radialLeftCorner_normal_mem (p - R.start) (R.chain.edge i) (R.chain.edge i) radial radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_first_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialLeftCornerFrame (p - R.start) (R.chain.edge i)) Real.pi Real.pi_pos
    (by linarith [Real.pi_pos]) banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p] using! physical y

end Unfoldings.PolygonalRay
