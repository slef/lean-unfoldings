module

public import Unfoldings.Convex.CommonPotential
public import Unfoldings.Geometry.PolygonalLength

/-! Common-potential estimates on actual polygonal paths, including all merger histories. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope) {n : ℕ} (P : PolygonalChain Plane n)

/-- Slopes can change independently from edge to edge; one convex potential still telescopes. -/
theorem path_progress {c : ℝ}
    (choices : ∀ i, ∃ p, E.Active (P.vertex i.castSucc) p ∧
      c * ‖P.edge i‖ ≤ inner ℝ p (P.edge i)) :
    c * P.projectedLength ≤ E.height (P.vertex (Fin.last n)) - E.height (P.vertex 0) := by
  apply P.potential_progress E.height
  intro i
  obtain ⟨p, active, step⟩ := choices i
  have support := E.active_support active (P.vertex i.succ)
  rw [inner_sub_right] at support
  dsimp [PolygonalChain.edge] at step ⊢
  rw [inner_sub_right] at step
  linarith

theorem path_length_bound {b c : ℝ} (positive : 0 < c)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    (choices : ∀ i, ∃ p, E.Active (P.vertex i.castSucc) p ∧
      c * ‖P.edge i‖ ≤ inner ℝ p (P.edge i)) :
    P.projectedLength ≤ (b / c) * ‖P.vertex (Fin.last n) - P.vertex 0‖ :=
  E.history_length_bound positive bounded (E.path_progress P choices)

/-- Every terminal active slope controls this entire actual incoming path. -/
theorem path_history_angle {b c : ℝ} (positive : 0 < b) (nonnegative : 0 ≤ c) (ratio : c ≤ b)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    (choices : ∀ i, ∃ p, E.Active (P.vertex i.castSucc) p ∧
      c * ‖P.edge i‖ ≤ inner ℝ p (P.edge i)) {p : Plane}
    (active : E.Active (P.vertex (Fin.last n)) p) (pne : p ≠ 0)
    (different : P.vertex (Fin.last n) ≠ P.vertex 0) :
    InnerProductGeometry.angle p (P.vertex (Fin.last n) - P.vertex 0) ≤ Real.arccos (c / b) :=
  E.history_angle_bound positive nonnegative ratio bounded active pne different
    (E.path_progress P choices) P.chord_le_projectedLength

end Unfoldings.SlopeEnvelope
