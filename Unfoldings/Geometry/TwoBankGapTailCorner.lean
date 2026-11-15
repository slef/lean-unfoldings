module

public import Unfoldings.Geometry.TwoBankGapBankSector
public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.RadialCornerSector

/-! Intrinsic gap charts at the bend into the actual infinite bank tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ (n + 1)) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The actual last finite bend has its original incoming edge and its entire outgoing
tail direction as banks. Their derived occupied corner gives a whole intrinsic ball chart. -/
theorem exists_first_terminal_vertex_chart (common : Q.start = R.start)
    (genuine : ∀ i : Fin (n + 1), R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (tail_radial : 0 < inner ℝ (R.chain.vertex (Fin.last (n + 1)) - R.start) R.direction) :
    let p := R.chain.vertex (Fin.last (n + 1))
    let incoming := p - R.chain.vertex (Fin.last n).castSucc
    let width := radialLeftCornerWidth (p - R.start) incoming R.direction
    let frame := radialLeftCornerFrame (p - R.start) R.direction
    ∃ (positive : 0 < width) (small : width < 2 * Real.pi),
      width = positiveGapAngle R.direction (-incoming) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
        (R.twoBankFirstBankPoint Q first_outward first_nonzero last_outward last_nonzero
          positive_phase common ‖p - R.start‖₊) (ENNReal.ofReal δ) ≃ᵢ
        Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
        ∀ y, p + frame ((bisectedSectorFan width positive small).develop (A y).val) =
          y.val.val := by
  dsimp only
  let p := R.chain.vertex (Fin.last (n + 1))
  let incoming := p - R.chain.vertex (Fin.last n).castSucc
  have first : 0 < inner ℝ (p - R.start) incoming :=
    R.inner_terminal_edge_pos first_outward (Fin.last n) (genuine (Fin.last n))
  obtain ⟨positive, small⟩ := radialLeftCornerWidth_bounds (p - R.start) incoming R.direction
    first tail_radial
  refine ⟨positive, small,
    radialLeftCornerWidth_eq_positiveGapAngle _ _ _ first tail_radial, ?_⟩
  let r := ‖p - R.start‖₊
  have actual : R.radialPoint first_outward first_nonzero r = p :=
    R.radialPoint_vertex first_outward first_nonzero (Fin.last (n + 1))
  have radius : 0 < r := by
    change 0 < ‖p - R.start‖
    apply norm_pos_iff.mpr
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have banks : R.complexCarrierGerm (R.radialPoint first_outward first_nonzero r) =
      radialLeftCornerFrame (p - R.start) R.direction ''
        (Set.range (fun t : ℝ≥0 => (t : ℂ)) ∪ Set.range (fun t : ℝ≥0 =>
          (t : ℂ) * polarRay (radialLeftCornerWidth (p - R.start) incoming R.direction))) := by
    rw [actual, R.complexCarrierGerm_terminal_vertex first_outward genuine]
    have backward : R.chain.vertex (Fin.last n).castSucc - p = -incoming := by
      dsimp [incoming]
      abel
    rw [backward]
    exact radialLeftCorner_bank_rays _ _ _ first tail_radial
  have normal : Complex.I * (R.radialPoint first_outward first_nonzero r - R.start) ∈
      interior (radialLeftCornerFrame (p - R.start) R.direction ''
        closedAngularSector (radialLeftCornerWidth (p - R.start) incoming R.direction)) := by
    rw [actual]
    exact radialLeftCorner_normal_mem _ _ _ first tail_radial
  obtain ⟨δ, δpos, A, physical⟩ := R.exists_first_bank_sector_chart Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius
    (radialLeftCornerFrame (p - R.start) R.direction)
    (radialLeftCornerWidth (p - R.start) incoming R.direction) positive small banks normal
  refine ⟨δ, δpos, A, ?_⟩
  intro y
  simpa only [actual, p, incoming] using! physical y

end Unfoldings.PolygonalRay
