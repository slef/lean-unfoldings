module

public import Unfoldings.Complex.DirectedCutBank
public import Unfoldings.Complex.BoundaryCycleEnumeration
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.ChainOfFn

/-! Extract original seam-side-endpoint labels from actual cut-bank chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- An actual bank created by a cut has its original seam, side and endpoint labels. -/
theorem exists_directedCutBank_start (p : C.BoundaryEnd retain)
    (cut : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p.val)) :
    ∃ bank : C.DirectedCutBank retain, bank.start = p := by
  classical
  have paired : ∃ s, C.Incident s (C.germEdge p.val) := by
    by_contra absent
    apply cut
    rintro ⟨s, _kept, incident⟩
    exact absent ⟨s, incident⟩
  obtain ⟨s, incident⟩ := paired
  have not_kept : s ∉ retain := fun kept => p.property ⟨s, kept, incident⟩
  rcases incident with first | last
  · refine ⟨⟨⟨s, not_kept⟩, false, p.val.2⟩, ?_⟩
    apply (C.boundaryEndEquiv retain).injective
    simp only [DirectedCutBank.start, DirectedCutBank.bank, Equiv.apply_symm_apply]
    exact Prod.ext (Subtype.ext first.symm) rfl
  · refine ⟨⟨⟨s, not_kept⟩, true, p.val.2⟩, ?_⟩
    apply (C.boundaryEndEquiv retain).injective
    simp only [DirectedCutBank.start, DirectedCutBank.bank, Equiv.apply_symm_apply]
    exact Prod.ext (Subtype.ext last.symm) rfl

/-- Actual cut-bank chains supply a nonrepeating original label path, with their exact
retained corner joins. No parent-bank enumeration or label certificate is supplied. -/
theorem exists_directed_cut_bank_chain_labels {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (chain.point i).val)) :
    ∃ label : Fin (n + 1) → C.DirectedCutBank retain,
      (∀ i, (label i).start = chain.point i) ∧
      (List.ofFn label).Pairwise (fun a b => a.bank ≠ b.bank) ∧
      (List.ofFn label).IsChain (fun a b =>
        C.vertexOfCorner retain a.finishCorner = C.vertexOfCorner retain b.startCorner) := by
  classical
  choose label named using fun i => C.exists_directedCutBank_start (chain.point i) (cut i)
  refine ⟨label, named, ?_, ?_⟩
  · apply List.pairwise_ofFn.mpr
    intro i j before same
    have actual : (C.boundaryEndEquiv retain (chain.point i)).1 =
        (C.boundaryEndEquiv retain (chain.point j)).1 := by
      rw [← named i, ← named j]
      simpa only [DirectedCutBank.start, Equiv.apply_symm_apply] using same
    exact (ne_of_lt before) ((C.boundaryChain_banks_injective retain chain) actual)
  · apply List.isChain_ofFn.mpr
    intro i bound
    let k : Fin n := ⟨i, by omega⟩
    rw [← (label _).finish_vertex, ← (label _).start_vertex, named, named]
    have step : C.boundaryMate retain (C.boundaryTurn retain (chain.point k.castSucc)) =
        chain.point k.succ := chain.next k
    have same := (C.boundaryMate_spec retain (C.boundaryTurn retain (chain.point k.castSucc))).2
    rw [step] at same
    exact same.symm

end Unfoldings.TriangleComplex
