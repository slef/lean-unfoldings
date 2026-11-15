module

public import Unfoldings.Topology.ChainConcatRange
public import Mathlib.Data.List.Chain

/-! Assemble any nonempty finite ordered family of separated actual interval chains. -/

@[expose] public section

namespace PairedInvolutions.System

universe u

variable {X : Type u} (P : System X)

/-- Actual chains may have different numbers of original labeled intervals. -/
abbrev ChainBlock := Σ n, P.Chain n

/-- Blocks are separated in both bank orientations. -/
def ChainBlocksSeparated (A B : P.ChainBlock) : Prop :=
  ∀ i j, A.2.point i ≠ B.2.point j ∧ A.2.point i ≠ P.turn (B.2.point j)

/-- A join uses the actual successor, not a geometric placement or an assumed fan match. -/
def ChainBlocksJoined (A B : P.ChainBlock) : Prop := P.mate (P.turn A.2.last) = B.2.first

/-- Assemble all blocks in order. Every original directed interval occurs, with its
orientation preserved, and no additional interval is inserted. -/
theorem exists_chain_of_blocks (blocks : List P.ChainBlock) (nonempty : blocks ≠ [])
    (separated : blocks.Pairwise P.ChainBlocksSeparated)
    (joined : blocks.IsChain P.ChainBlocksJoined) :
    ∃ n, ∃ chain : P.Chain n,
      chain.first = (blocks.head nonempty).2.first ∧
      chain.last = (blocks.getLast nonempty).2.last ∧
      ∀ x, (∃ i, chain.point i = x) ↔ ∃ block ∈ blocks, ∃ i, block.2.point i = x := by
  induction blocks with
  | nil => exact (nonempty rfl).elim
  | cons A tail previous =>
    cases tail with
    | nil =>
      refine ⟨A.1, A.2, rfl, rfl, ?_⟩
      intro x
      simp only [List.mem_singleton, exists_eq_left]
    | cons B rest =>
      obtain ⟨apart, tail_apart⟩ := List.pairwise_cons.mp separated
      obtain ⟨step, tail_joined⟩ := List.isChain_cons_cons.mp joined
      obtain ⟨n, chain, first, last, covered⟩ := previous (by simp) tail_apart tail_joined
      have join : P.mate (P.turn A.2.last) = chain.first := by
        rw [first]
        exact step
      have distinct : ∀ i j, A.2.point i ≠ chain.point j ∧
          A.2.point i ≠ P.turn (chain.point j) := by
        intro i j
        obtain ⟨block, member, k, equal⟩ := (covered (chain.point j)).mp ⟨j, rfl⟩
        simpa only [equal] using apart block member i k
      let all := A.2.concat chain distinct join
      refine ⟨A.1 + n + 1, all, ?_, ?_, ?_⟩
      · exact A.2.concat_first chain distinct join
      · simpa only [List.getLast_cons_cons] using
          (A.2.concat_last chain distinct join).trans last
      · intro x
        rw [A.2.concat_point_range_iff chain distinct join, covered]
        simp only [List.mem_cons]
        constructor
        · rintro (first | ⟨block, member, point⟩)
          · exact ⟨A, Or.inl rfl, first⟩
          · exact ⟨block, Or.inr member, point⟩
        · rintro ⟨block, (rfl | member), point⟩
          · exact Or.inl point
          · exact Or.inr ⟨block, member, point⟩

end PairedInvolutions.System
