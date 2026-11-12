module

public import Unfoldings.Geometry.SubdivisionNonemptyBoundary
public import Unfoldings.Topology.FilterBoundaryRuns
public import Unfoldings.Topology.IndexedBoundaryRun

/-! Filtered extreme cells retain actual indexed boundary runs or enclosing-bank contacts. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

structure BoundaryRun (cutoff : ℝ) (keep : {T : MonotoneStrip // T ∈ P.cells} → Bool)
    (source : {T : MonotoneStrip // T ∈ P.cells}) (upper : Bool) where
  length : ℕ
  cells : Fin (length + 1) → {T : MonotoneStrip // T ∈ P.cells}
  physical : ∀ k, ((cells k).val.openSlab 0 cutoff).Nonempty
  removed : ∀ k, ¬ keep (cells k)
  contacts : ∀ k : Fin length, Set.EqOn (cells k.castSucc).val.upper.point
    (cells k.succ).val.lower.point (Set.Icc 0 cutoff)
  ordered : ∀ a b : Fin (length + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach
  source_order : if upper then ∀ k, List.Sublist [source, cells k] P.cells.attach
    else ∀ k, List.Sublist [cells k, source] P.cells.attach
  facing : if upper then
    Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff)
    else Set.EqOn source.val.lower.point (cells (Fin.last length)).val.upper.point
      (Set.Icc 0 cutoff)
  outer : if upper then
    Set.EqOn (cells (Fin.last length)).val.upper.point S.upper.point (Set.Icc 0 cutoff)
    else Set.EqOn S.lower.point (cells 0).val.lower.point (Set.Icc 0 cutoff)

theorem lower_boundary_run_or_contact {cutoff : ℝ} (positive : 0 < cutoff)
    (keep : {T : MonotoneStrip // T ∈ P.cells} → Bool)
    (source : {T : MonotoneStrip // T ∈ P.cells})
    (at_head : ((P.nonemptyCells cutoff).filter keep).head? = some source) :
    Set.EqOn S.lower.point source.val.lower.point (Set.Icc 0 cutoff) ∨
      Nonempty (P.BoundaryRun cutoff keep source false) := by
  obtain ⟨before, after, equal, removed, _⟩ :=
    filter_head_boundary_run keep (P.nonemptyCells cutoff) at_head
  cases before with
  | nil =>
    left
    apply P.nonemptyCells_head_contact positive source
    rw [equal]
    rfl
  | cons head tail =>
    let cells : Fin (tail.length + 1) → {T : MonotoneStrip // T ∈ P.cells} := (head :: tail).get
    obtain ⟨contacts, ordered, source_order, facing, at_start⟩ := indexed_initial_run_data
      (P.nonemptyCells cutoff) head source tail after equal
      (P.nonemptyCells_bank_contact_chain positive)
    have members (k : Fin (tail.length + 1)) : cells k ∈ P.nonemptyCells cutoff := by
      rw [equal]
      exact List.mem_append_left _ (List.get_mem _ _)
    refine Or.inr ⟨{
      length := tail.length
      cells := cells
      physical := fun k => (P.mem_nonemptyCells cutoff (cells k)).mp (members k)
      removed := fun k => removed _ (List.get_mem _ _)
      contacts := contacts
      ordered := fun a b before => (ordered a b before).trans (P.nonemptyCells_sublist cutoff)
      source_order := fun k => (source_order k).trans (P.nonemptyCells_sublist cutoff)
      facing := fun h member => (facing member).symm
      outer := P.nonemptyCells_head_contact positive (cells 0) at_start }⟩

theorem upper_boundary_run_or_contact {cutoff : ℝ} (positive : 0 < cutoff)
    (keep : {T : MonotoneStrip // T ∈ P.cells} → Bool)
    (source : {T : MonotoneStrip // T ∈ P.cells})
    (at_last : ((P.nonemptyCells cutoff).filter keep).getLast? = some source) :
    Set.EqOn source.val.upper.point S.upper.point (Set.Icc 0 cutoff) ∨
      Nonempty (P.BoundaryRun cutoff keep source true) := by
  obtain ⟨before, after, equal, _, removed⟩ :=
    filter_last_boundary_run keep (P.nonemptyCells cutoff) at_last
  cases after with
  | nil =>
    left
    apply P.nonemptyCells_last_contact positive source
    rw [equal, List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or]
  | cons head tail =>
    let cells : Fin (tail.length + 1) → {T : MonotoneStrip // T ∈ P.cells} := (head :: tail).get
    obtain ⟨contacts, ordered, source_order, facing, at_end⟩ := indexed_final_run_data
      (P.nonemptyCells cutoff) source head tail before equal
      (P.nonemptyCells_bank_contact_chain positive)
    have members (k : Fin (tail.length + 1)) : cells k ∈ P.nonemptyCells cutoff := by
      rw [equal]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.get_mem _ _))
    exact Or.inr ⟨{
      length := tail.length
      cells := cells
      physical := fun k => (P.mem_nonemptyCells cutoff (cells k)).mp (members k)
      removed := fun k => removed _ (List.get_mem _ _)
      contacts := contacts
      ordered := fun a b before => (ordered a b before).trans (P.nonemptyCells_sublist cutoff)
      source_order := fun k => (source_order k).trans (P.nonemptyCells_sublist cutoff)
      facing := facing
      outer := P.nonemptyCells_last_contact positive (cells (Fin.last tail.length)) at_end }⟩

end Unfoldings.MonotoneStrip.Subdivision
