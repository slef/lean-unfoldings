module

public import Unfoldings.Roof.CompletionBankBlocks
public import Unfoldings.Complex.DirectedCutBank
public import Unfoldings.Topology.ChainBlockAssembly

/-! Assemble complete physical refinements of finite original directed cut-bank paths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionPathAssemblyIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- A finite original bank path constructs one whole actual fine boundary chain. Original
bank distinctness and retained corner joins derive all fine successors. Its exact directed
labels are precisely those of the complete canonical physical bank refinements. -/
theorem exists_original_bank_path_refinement (retain : Set C.Seam)
    (banks : List (C.DirectedCutBank retain)) (nonempty : banks ≠ [])
    (different : banks.Pairwise (fun a b => a.bank ≠ b.bank))
    (joined : banks.IsChain (fun a b =>
      C.vertexOfCorner retain a.finishCorner = C.vertexOfCorner retain b.startCorner)) :
    ∃ n : ℕ, ∃ chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain n,
      E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain) chain.first)) =
          C.vertexPoint retain (C.vertexOfCorner retain (banks.head nonempty).startCorner) ∧
      E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
          (E.originalComplex.boundaryTurn (E.originalRetain retain) chain.last))) =
          C.vertexPoint retain (C.vertexOfCorner retain (banks.getLast nonempty).finishCorner) ∧
      ∀ p : E.originalComplex.BoundaryEnd (E.originalRetain retain),
        (∃ i, chain.point i = p) ↔ ∃ bank ∈ banks, ∃ i,
          (E.originalBankBlock retain bank.seam bank.side bank.flag).chain.point i = p := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let P := D.boundarySystem kept
  let block (bank : C.DirectedCutBank retain) :=
    E.originalBankBlock retain bank.seam bank.side bank.flag
  let blockData (bank : C.DirectedCutBank retain) : P.ChainBlock :=
    ⟨(block bank).length, (block bank).chain⟩
  let pieces : List P.ChainBlock := banks.map blockData
  have pieces_nonempty : pieces ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  have apart : pieces.Pairwise P.ChainBlocksSeparated := by
    apply List.pairwise_map.mpr
    exact different.imp (fun {_ _} distinct => (block _).separated (block _) distinct)
  have fine_joined : pieces.IsChain P.ChainBlocksJoined := by
    apply (List.isChain_map _).mpr
    apply List.isChain_iff_getElem.mpr
    intro i bound
    exact (block banks[i]).joined (block banks[i + 1])
      (List.isChain_iff_getElem.mp different.isChain i bound)
      (List.isChain_iff_getElem.mp joined i bound)
  obtain ⟨n, chain, first, last, covered⟩ := P.exists_chain_of_blocks pieces pieces_nonempty
    apart fine_joined
  have first_eq : chain.first = (block (banks.head nonempty)).chain.first := by
    exact first.trans (congrArg (fun piece : P.ChainBlock => piece.2.first)
      (List.head_map (f := blockData) pieces_nonempty))
  have last_eq : chain.last = (block (banks.getLast nonempty)).chain.last := by
    exact last.trans (congrArg (fun piece : P.ChainBlock => piece.2.last)
      (List.getLast_map (f := blockData) pieces_nonempty))
  refine ⟨n, chain, ?_, ?_, ?_⟩
  · rw [first_eq]
    exact (block (banks.head nonempty)).first_image
  · rw [last_eq]
    exact (block (banks.getLast nonempty)).last_image
  · intro p
    rw [covered]
    constructor
    · rintro ⟨piece, member, i, equal⟩
      obtain ⟨bank, present, rfl⟩ := List.mem_map.mp member
      exact ⟨bank, present, i, equal⟩
    · rintro ⟨bank, present, i, equal⟩
      exact ⟨⟨(block bank).length, (block bank).chain⟩, List.mem_map.mpr ⟨bank, present, rfl⟩,
        i, equal⟩

end Unfoldings.ConvexRoof.CompletionMesh
