module

public import Unfoldings.Geometry.SubdivisionCellChain
public import Unfoldings.Geometry.EmptyStripBanks
public import Unfoldings.Topology.ChainIdentityContraction

/-! Removing physically empty cells retains exact bank contacts on the controlled closed slab. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

def nonemptyCells (cutoff : ℝ) : List {T : MonotoneStrip // T ∈ P.cells} := by
  classical
  exact P.cells.attach.filter (fun cell => decide (cell.val.openSlab 0 cutoff).Nonempty)

@[simp] theorem mem_nonemptyCells (cutoff : ℝ) (cell : {T : MonotoneStrip // T ∈ P.cells}) :
    cell ∈ P.nonemptyCells cutoff ↔ (cell.val.openSlab 0 cutoff).Nonempty := by
  classical
  simp only [nonemptyCells, List.mem_filter, List.mem_attach, decide_eq_true_eq, true_and]

theorem nonemptyCells_sublist (cutoff : ℝ) :
    List.Sublist (P.nonemptyCells cutoff) P.cells.attach := List.filter_sublist

/-- The result concerns the same physical slab. It imposes no identity on
arbitrary extensions of the two wall functions outside that slab. -/
theorem nonemptyCells_bank_contact_chain {cutoff : ℝ} (positive : 0 < cutoff) :
    (P.nonemptyCells cutoff).IsChain (fun A B =>
      Set.EqOn A.val.upper.point B.val.lower.point (Set.Icc 0 cutoff)) := by
  classical
  let first := fun cell : {T : MonotoneStrip // T ∈ P.cells} =>
    fun h : Set.Icc (0 : ℝ) cutoff => cell.val.lower.point h.val
  let last := fun cell : {T : MonotoneStrip // T ∈ P.cells} =>
    fun h : Set.Icc (0 : ℝ) cutoff => cell.val.upper.point h.val
  have attached : P.cells.attach.IsChain (fun A B => last A = first B) := by
    apply List.isChain_attach.mpr
    exact List.IsChain.imp_of_mem_imp (fun A B left right equal => ⟨left, right, by
      change (fun h : Set.Icc (0 : ℝ) cutoff => A.upper.point h.val) =
        (fun h : Set.Icc (0 : ℝ) cutoff => B.lower.point h.val)
      rw [equal]⟩) P.cells_chain
  have filtered : (P.nonemptyCells cutoff).IsChain (fun A B => last A = first B) := by
    unfold nonemptyCells
    apply chain_filter_of_removed_identity first last _ P.cells.attach attached
    intro cell _ removed
    have empty : cell.val.openSlab 0 cutoff = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false removed)
    exact funext (fun h => cell.val.banks_point_eqOn_of_empty_openSlab positive empty h.property)
  exact filtered.imp (fun A B equal h member => congrFun equal ⟨h, member⟩)

end Unfoldings.MonotoneStrip.Subdivision
