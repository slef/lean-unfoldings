module

public import Unfoldings.Roof.CompletionBankPathAssembly
public import Unfoldings.Complex.DirectedBankChain

/-! Complete physical fine refinements extracted from actual original cut-bank chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionOriginalChainIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- An actual original chain whose banks were created by cuts constructs one whole fine
boundary chain. Its labels, successor order and exact metric endpoint copies are derived.
Every directed fine bank is precisely a piece of one of its original directed banks. -/
theorem exists_original_chain_refinement (retain : Set C.Seam) {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (chain.point i).val)) :
    ∃ label : Fin (n + 1) → C.DirectedCutBank retain,
      (∀ i, (label i).start = chain.point i) ∧
      ∃ m : ℕ, ∃ fine : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain m,
        E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
          (E.originalComplex.boundaryEndVertex (E.originalRetain retain) fine.first)) =
            C.vertexPoint retain (C.boundaryEndVertex retain chain.first) ∧
        E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
          (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
            (E.originalComplex.boundaryTurn (E.originalRetain retain) fine.last))) =
            C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last)) ∧
        ∀ p : E.originalComplex.BoundaryEnd (E.originalRetain retain),
          (∃ j, fine.point j = p) ↔ ∃ i : Fin (n + 1), ∃ j,
            (E.originalBankBlock retain (label i).seam
              (label i).side (label i).flag).chain.point j = p := by
  obtain ⟨label, named, different, joined⟩ := C.exists_directed_cut_bank_chain_labels chain cut
  let banks := List.ofFn label
  have nonempty : banks ≠ [] := by
    intro empty
    have zero := List.ofFn_eq_nil_iff.mp empty
    omega
  obtain ⟨m, fine, first, last, covered⟩ := E.exists_original_bank_path_refinement retain banks
    nonempty different joined
  have head : banks.head nonempty = label 0 := List.head_ofFn nonempty
  have tail : banks.getLast nonempty = label (Fin.last n) := by
    simpa only [Nat.add_sub_cancel] using! List.getLast_ofFn (f := label) nonempty
  refine ⟨label, named, m, fine, ?_, ?_, ?_⟩
  · rw [first, head, ← (label 0).start_vertex, named]
    rfl
  · rw [last, tail, ← (label (Fin.last n)).finish_vertex, named]
    rfl
  · intro p
    rw [covered]
    constructor
    · rintro ⟨bank, member, j, equal⟩
      obtain ⟨i, at_i⟩ := List.mem_ofFn.mp member
      subst bank
      exact ⟨i, j, equal⟩
    · rintro ⟨i, j, equal⟩
      exact ⟨label i, List.mem_ofFn.mpr ⟨i, rfl⟩, j, equal⟩

end Unfoldings.ConvexRoof.CompletionMesh
