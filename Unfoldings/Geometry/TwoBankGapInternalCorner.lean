module

public import Unfoldings.Geometry.TwoBankGapBankSector
public import Unfoldings.Geometry.PolygonalBankVertexGerm
public import Unfoldings.Geometry.RadialVertexCoordinates
public import Unfoldings.Geometry.RadialCornerSector

/-! Derive intrinsic gap charts at named original internal bank vertices. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ (n + 2)) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The actual intrinsic gap point at a named original vertex of its first bank. -/
def twoBankFirstVertexPoint (common : Q.start = R.start) (i : Fin (n + 3)) :
    PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) :=
  R.twoBankFirstBankPoint Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common ‖R.chain.vertex i - R.start‖₊

@[simp] theorem twoBankFirstVertexPoint_val (common : Q.start = R.start)
    (i : Fin (n + 3)) :
    (R.twoBankFirstVertexPoint Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common i).val = R.chain.vertex i :=
  R.radialPoint_vertex first_outward first_nonzero i

/-- At an actual internal bank bend, original outward edges determine the sector aperture,
its physical frame, and a whole intrinsic fan-ball chart. The incoming radial positivity,
incident ray pair, and occupied side are derived, rather than supplied as corner models. -/
theorem exists_first_internal_vertex_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin (n + 2), R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (k : Fin (n + 1))
    (outgoing_radial : 0 < inner ℝ (R.chain.vertex k.succ.castSucc - R.start)
      (R.chain.vertex k.succ.succ - R.chain.vertex k.succ.castSucc)) :
    let p := R.chain.vertex k.succ.castSucc
    let incoming := p - R.chain.vertex k.castSucc.castSucc
    let outgoing := R.chain.vertex k.succ.succ - p
    let width := radialLeftCornerWidth (p - R.start) incoming outgoing
    let frame := radialLeftCornerFrame (p - R.start) outgoing
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      width = positiveGapAngle outgoing (-incoming) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankFirstVertexPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common k.succ.castSucc) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  let p := R.chain.vertex k.succ.castSucc
  let incoming := p - R.chain.vertex k.castSucc.castSucc
  let outgoing := R.chain.vertex k.succ.succ - p
  have first : 0 < inner ℝ (p - R.start) incoming := by
    simpa only [Fin.succ_castSucc] using
      R.inner_terminal_edge_pos first_outward k.castSucc (genuine k.castSucc)
  obtain ⟨positive, small⟩ := radialLeftCornerWidth_bounds (p - R.start) incoming outgoing
    first outgoing_radial
  refine ⟨positive, small,
    radialLeftCornerWidth_eq_positiveGapAngle _ _ _ first outgoing_radial, ?_⟩
  let r := ‖p - R.start‖₊
  have actual : R.radialPoint first_outward first_nonzero r = p :=
    R.radialPoint_vertex first_outward first_nonzero k.succ.castSucc
  have radius : 0 < r := by
    change 0 < ‖p - R.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have banks : R.complexCarrierGerm (R.radialPoint first_outward first_nonzero r) =
      radialLeftCornerFrame (p - R.start) outgoing ''
        (Set.range (fun t : ℝ≥0 => (t : ℂ)) ∪ Set.range (fun t : ℝ≥0 =>
          (t : ℂ) * polarRay (radialLeftCornerWidth (p - R.start) incoming outgoing))) := by
    rw [actual, R.complexCarrierGerm_internal_vertex first_outward first_nonzero genuine k]
    have backward : R.chain.vertex k.castSucc.castSucc - p = -incoming := by
      dsimp [incoming]
      abel
    rw [backward]
    exact radialLeftCorner_bank_rays _ _ _ first outgoing_radial
  have normal : Complex.I * (R.radialPoint first_outward first_nonzero r - R.start) ∈
      interior (radialLeftCornerFrame (p - R.start) outgoing ''
        closedAngularSector (radialLeftCornerWidth (p - R.start) incoming outgoing)) := by
    rw [actual]
    exact radialLeftCorner_normal_mem _ _ _ first outgoing_radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_first_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialLeftCornerFrame (p - R.start) outgoing)
    (radialLeftCornerWidth (p - R.start) incoming outgoing) positive small banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p, incoming, outgoing] using! physical y

end Unfoldings.PolygonalRay
