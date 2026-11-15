module

public import Unfoldings.Geometry.TwoBankGapSecondSector
public import Unfoldings.Geometry.PolygonalBankVertexGerm
public import Unfoldings.Geometry.RadialVertexCoordinates
public import Unfoldings.Geometry.RadialRightCorner

/-! Derive intrinsic gap charts at named original internal bank vertices. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ (m + 2))
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The actual intrinsic gap point at a named original vertex of its second bank. -/
def twoBankSecondVertexPoint (common : Q.start = R.start) (i : Fin (m + 3)) :
    PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) :=
  R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common ‖Q.chain.vertex i - Q.start‖₊

@[simp] theorem twoBankSecondVertexPoint_val (common : Q.start = R.start)
    (i : Fin (m + 3)) :
    (R.twoBankSecondVertexPoint Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common i).val = Q.chain.vertex i :=
  Q.radialPoint_vertex last_outward last_nonzero i

/-- At an actual internal bank bend, original outward edges determine the sector aperture,
its physical frame, and a whole intrinsic fan-ball chart. The incoming radial positivity,
incident ray pair, and occupied side are derived, rather than supplied as corner models. -/
theorem exists_second_internal_vertex_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin (m + 2), Q.chain.vertex i.castSucc ≠ Q.chain.vertex i.succ)
    (k : Fin (m + 1))
    (outgoing_radial : 0 < inner ℝ (Q.chain.vertex k.succ.castSucc - Q.start)
      (Q.chain.vertex k.succ.succ - Q.chain.vertex k.succ.castSucc)) :
    let p := Q.chain.vertex k.succ.castSucc
    let incoming := p - Q.chain.vertex k.castSucc.castSucc
    let outgoing := Q.chain.vertex k.succ.succ - p
    let width := radialRightCornerWidth (p - Q.start) incoming outgoing
    let frame := radialRightCornerFrame (p - Q.start) incoming
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      width = positiveGapAngle (-incoming) outgoing ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankSecondVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  let p := Q.chain.vertex k.succ.castSucc
  let incoming := p - Q.chain.vertex k.castSucc.castSucc
  let outgoing := Q.chain.vertex k.succ.succ - p
  have first : 0 < inner ℝ (p - Q.start) incoming := by
    simpa only [Fin.succ_castSucc] using
      Q.inner_terminal_edge_pos last_outward k.castSucc (genuine k.castSucc)
  obtain ⟨positive, small⟩ := radialRightCornerWidth_bounds (p - Q.start) incoming outgoing
    first outgoing_radial
  refine ⟨positive, small,
    radialRightCornerWidth_eq_positiveGapAngle _ _ _ first outgoing_radial, ?_⟩
  let r := ‖p - Q.start‖₊
  have actual : Q.radialPoint last_outward last_nonzero r = p :=
    Q.radialPoint_vertex last_outward last_nonzero k.succ.castSucc
  have radius : 0 < r := by
    change 0 < ‖p - Q.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have banks : Q.complexCarrierGerm (Q.radialPoint last_outward last_nonzero r) =
      radialRightCornerFrame (p - Q.start) incoming ''
        (Set.range (fun t : ℝ≥0 => (t : ℂ)) ∪ Set.range (fun t : ℝ≥0 =>
          (t : ℂ) * polarRay (radialRightCornerWidth (p - Q.start) incoming outgoing))) := by
    rw [actual, Q.complexCarrierGerm_internal_vertex last_outward last_nonzero genuine k]
    have backward : Q.chain.vertex k.castSucc.castSucc - p = -incoming := by
      dsimp [incoming]
      abel
    rw [backward]
    exact radialRightCorner_bank_rays _ _ _ first outgoing_radial
  have normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior (radialRightCornerFrame (p - Q.start) incoming ''
        closedAngularSector (radialRightCornerWidth (p - Q.start) incoming outgoing)) := by
    rw [actual]
    exact radialRightCorner_normal_mem _ _ _ first outgoing_radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_second_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialRightCornerFrame (p - Q.start) incoming)
    (radialRightCornerWidth (p - Q.start) incoming outgoing) positive small banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p, incoming, outgoing] using! physical y

end Unfoldings.PolygonalRay
