module

public import Unfoldings.Geometry.PolygonalRayOpening
public import Unfoldings.Geometry.TerminalEdgeRay

/-! Openings through the last edge's start preserve a straight terminal continuation. -/

@[expose] public section

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ (n + 1))

/-- A hinge at or before the last edge's initial point rotates the edge and the tail together. -/
theorem openings_straightTail (events : List (Opening (n + 1)))
    (before : ∀ e ∈ events, e.hinge ≤ (Fin.last n).castSucc)
    (straight : R.direction = R.chain.edge (Fin.last n)) :
    (R.openings events).direction = (R.openings events).chain.edge (Fin.last n) := by
  have heading : openingHeading events (Fin.last n) = openingTailHeading events := by
    unfold openingHeading openingTailHeading
    congr 1
    exact List.map_congr_left fun e he => by simp [before e he]
  rw [openings_direction, openings_chain, R.chain.openings_edge, heading, straight]

end Unfoldings.PolygonalRay
