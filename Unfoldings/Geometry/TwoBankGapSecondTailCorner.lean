module

public import Unfoldings.Geometry.TwoBankGapSecondSector
public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.RadialRightCorner

/-! Intrinsic gap charts at the bend into the actual infinite bank tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ (m + 1))
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The actual last finite bend has its original incoming edge and its entire outgoing
tail direction as banks. Their derived occupied corner gives a whole intrinsic ball chart. -/
theorem exists_second_terminal_vertex_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin (m + 1), Q.chain.vertex i.castSucc ≠ Q.chain.vertex i.succ)
    (tail_radial : 0 < inner ℝ (Q.chain.vertex (Fin.last (m + 1)) - Q.start) Q.direction) :
    let p := Q.chain.vertex (Fin.last (m + 1))
    let incoming := p - Q.chain.vertex (Fin.last m).castSucc
    let width := radialRightCornerWidth (p - Q.start) incoming Q.direction
    let frame := radialRightCornerFrame (p - Q.start) incoming
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      width = positiveGapAngle (-incoming) Q.direction ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common ‖p - Q.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  let p := Q.chain.vertex (Fin.last (m + 1))
  let incoming := p - Q.chain.vertex (Fin.last m).castSucc
  have first : 0 < inner ℝ (p - Q.start) incoming :=
    Q.inner_terminal_edge_pos last_outward (Fin.last m) (genuine (Fin.last m))
  obtain ⟨positive, small⟩ := radialRightCornerWidth_bounds (p - Q.start) incoming Q.direction
    first tail_radial
  refine ⟨positive, small,
    radialRightCornerWidth_eq_positiveGapAngle _ _ _ first tail_radial, ?_⟩
  let r := ‖p - Q.start‖₊
  have actual : Q.radialPoint last_outward last_nonzero r = p :=
    Q.radialPoint_vertex last_outward last_nonzero (Fin.last (m + 1))
  have radius : 0 < r := by
    change 0 < ‖p - Q.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have banks : Q.complexCarrierGerm (Q.radialPoint last_outward last_nonzero r) =
      radialRightCornerFrame (p - Q.start) incoming ''
        (Set.range (fun t : ℝ≥0 => (t : ℂ)) ∪ Set.range (fun t : ℝ≥0 =>
          (t : ℂ) * polarRay (radialRightCornerWidth (p - Q.start) incoming Q.direction))) := by
    rw [actual, Q.complexCarrierGerm_terminal_vertex last_outward genuine]
    have backward : Q.chain.vertex (Fin.last m).castSucc - p = -incoming := by
      dsimp [incoming]
      abel
    rw [backward]
    exact radialRightCorner_bank_rays _ _ _ first tail_radial
  have normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior (radialRightCornerFrame (p - Q.start) incoming ''
        closedAngularSector (radialRightCornerWidth (p - Q.start) incoming Q.direction)) := by
    rw [actual]
    exact radialRightCorner_normal_mem _ _ _ first tail_radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_second_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialRightCornerFrame (p - Q.start) incoming)
    (radialRightCornerWidth (p - Q.start) incoming Q.direction) positive small banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p, incoming] using! physical y

end Unfoldings.PolygonalRay
