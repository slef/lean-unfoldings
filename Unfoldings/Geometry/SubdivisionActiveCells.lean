module

public import Unfoldings.Geometry.SubdivisionCellChain
public import Unfoldings.Geometry.SubdivisionWallContacts
public import Unfoldings.Topology.ChainIdentityContraction

/-! Positive-width cells retain exact physical bank contacts after collapsed cells are skipped. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

/-- Membership in the same original subdivision remains part of every entry. -/
def activeCells (h : ℝ) : List {T : MonotoneStrip // T ∈ P.cells} :=
  P.cells.attach.filter (fun cell =>
    decide (cell.val.lower.coordinate h < cell.val.upper.coordinate h))

@[simp] theorem mem_activeCells (h : ℝ) (cell : {T : MonotoneStrip // T ∈ P.cells}) :
    cell ∈ P.activeCells h ↔ cell.val.lower.coordinate h < cell.val.upper.coordinate h := by
  simp only [activeCells, List.mem_filter, List.mem_attach, decide_eq_true_eq, true_and]

/-- Arbitrarily many consecutive zero-width cells leave no physical gap
between the surviving banks at this same height. -/
theorem activeCells_coordinate_chain (h : ℝ) :
    (P.activeCells h).IsChain (fun A B =>
      A.val.upper.coordinate h = B.val.lower.coordinate h) := by
  have attached : P.cells.attach.IsChain (fun A B =>
      A.val.upper.coordinate h = B.val.lower.coordinate h) := by
    apply List.isChain_attach.mpr
    exact List.IsChain.imp_of_mem_imp
      (fun A B first last equal => ⟨first, last,
        congrArg (fun G : MonotoneHeightGraph => G.coordinate h) equal⟩) P.cells_chain
  apply chain_filter_of_removed_identity
    (fun cell : {T : MonotoneStrip // T ∈ P.cells} => cell.val.lower.coordinate h)
    (fun cell => cell.val.upper.coordinate h) _ P.cells.attach attached
  intro cell _ removed
  have inactive : ¬ cell.val.lower.coordinate h < cell.val.upper.coordinate h :=
    of_decide_eq_false removed
  exact le_antisymm (cell.val.ordered h) (not_lt.mp inactive)

theorem activeCells_bank_point_chain (h : ℝ) :
    (P.activeCells h).IsChain (fun A B => A.val.upper.point h = B.val.lower.point h) :=
  (P.activeCells_coordinate_chain h).imp (fun A B equal =>
    A.val.upper.point_eq_of_same_coordinate B.val.lower equal)

end Unfoldings.MonotoneStrip.Subdivision
