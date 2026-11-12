module

public import Unfoldings.Geometry.SubdivisionNonemptyCells
public import Unfoldings.Topology.ChainFilterEndpoints

/-! The extreme surviving physical cells retain the original enclosing-strip banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

/-- Empty physical cells at either end may be discarded. The first and last
remaining bank functions still contact the enclosing strip on the whole
controlled slab, without any equality of their exterior continuations. -/
theorem nonemptyCells_endpoint_contacts {cutoff : ℝ} (positive : 0 < cutoff)
    (first last : {T : MonotoneStrip // T ∈ P.cells})
    (at_start : (P.nonemptyCells cutoff).head? = some first)
    (at_end : (P.nonemptyCells cutoff).getLast? = some last) :
    Set.EqOn S.lower.point first.val.lower.point (Set.Icc 0 cutoff) ∧
      Set.EqOn last.val.upper.point S.upper.point (Set.Icc 0 cutoff) := by
  classical
  let keep := fun cell : {T : MonotoneStrip // T ∈ P.cells} =>
    decide (cell.val.openSlab 0 cutoff).Nonempty
  have chain (h : ℝ) : P.cells.attach.IsChain (fun A B =>
      A.val.upper.point h = B.val.lower.point h) := by
    apply List.isChain_attach.mpr
    exact List.IsChain.imp_of_mem_imp (fun A B left right equal =>
      ⟨left, right, congrArg (fun G : MonotoneHeightGraph => G.point h) equal⟩) P.cells_chain
  have removed (h : ℝ) (height : h ∈ Set.Icc 0 cutoff)
      (cell : {T : MonotoneStrip // T ∈ P.cells}) (_ : cell ∈ P.cells.attach)
      (absent : keep cell = false) : cell.val.lower.point h = cell.val.upper.point h := by
    have empty : cell.val.openSlab 0 cutoff = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false absent)
    exact cell.val.banks_point_eqOn_of_empty_openSlab positive empty height
  constructor
  · intro h height
    have matched := chain_filter_head_of_removed_identity
      (fun cell : {T : MonotoneStrip // T ∈ P.cells} => cell.val.lower.point h)
      (fun cell : {T : MonotoneStrip // T ∈ P.cells} => cell.val.upper.point h)
      keep P.cells.attach (chain h) (removed h height) at_start
    have source : P.cells.attach.head?.map (fun cell => cell.val.lower.point h) =
        some (S.lower.point h) := by
      rw [← List.head?_map, List.attach_map_val
        (f := fun T : MonotoneStrip => T.lower.point h), List.head?_map]
      have original := congrArg (Option.map (fun G : MonotoneHeightGraph => G.point h))
        P.cells_head_lower
      simpa only [Option.map_map, Function.comp_def, Option.map_some] using original
    exact Option.some.inj (source.symm.trans matched)
  · intro h height
    have matched := chain_filter_last_of_removed_identity
      (fun cell : {T : MonotoneStrip // T ∈ P.cells} => cell.val.lower.point h)
      (fun cell : {T : MonotoneStrip // T ∈ P.cells} => cell.val.upper.point h)
      keep P.cells.attach (chain h) (removed h height) at_end
    have source : P.cells.attach.getLast?.map (fun cell => cell.val.upper.point h) =
        some (S.upper.point h) := by
      rw [← List.getLast?_map, List.attach_map_val
        (f := fun T : MonotoneStrip => T.upper.point h), List.getLast?_map]
      have original := congrArg (Option.map (fun G : MonotoneHeightGraph => G.point h))
        P.cells_last_upper
      simpa only [Option.map_map, Function.comp_def, Option.map_some] using original
    exact (Option.some.inj (source.symm.trans matched)).symm

end Unfoldings.MonotoneStrip.Subdivision
