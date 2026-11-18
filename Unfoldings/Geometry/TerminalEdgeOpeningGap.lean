module

public import Unfoldings.Geometry.TerminalEdgeRay
public import Unfoldings.Geometry.GlobalRadialChainTests
public import Unfoldings.Geometry.PositiveOpeningMarginGap

/-! All-anchor finite-bank estimates construct complete gaps on the actual terminal continuation. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ (n + 1))

/-- The final point stays a named hinge and the entire terminal ray remains outward. -/
theorem terminalEdgeRay_outward_of_global (radial : P.GloballyRadiallyMonotone) :
    P.terminalEdgeRay.Outward := P.terminalEdgeRay_outward (radial.outward P)

/-- No terminal or prefix length certificate is supplied: finite-bank margins derive them all. -/
theorem exists_terminalEdge_opening_gap (events : List (Opening (n + 1)))
    (nonzero : P.edge (Fin.last n) ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      (γ : ℝ) * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    let bank := P.terminalEdgeRay
    ∃ gap : Set ℂ,
      IsClosed gap ∧ frontier gap = bank.carrier ∪ (bank.openings events).carrier ∧
      bank.carrier ∩ (bank.openings events).carrier = {bank.start} ∧
      (interior gap).Nonempty ∧ closure (interior gap) = gap ∧
      CompleteSpace (PolygonalPoint gap) ∧ ContractibleSpace (PolygonalPoint gap) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        gap = ⋃ i, cells i :=
  P.terminalEdgeRay.exists_positive_opening_trace_gap_of_margin events nonzero γ positive small
    circle_budget margin (P.terminalEdgeRay_tail_margin positive.le small margin)
    angles_positive first at_start source_hinge

end Unfoldings.PolygonalChain
