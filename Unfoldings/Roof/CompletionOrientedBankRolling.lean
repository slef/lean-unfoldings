module

public import Unfoldings.Roof.CompletionBankRolling
public import Unfoldings.Complex.ReversedBoundaryChain

/-! Exact physical fine bank refinements in either original directed endpoint order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionOrientedBankIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Every directed old bank has a complete actual fine chain in its prescribed direction.
All physical pieces occur once, both true endpoint positions are correct and every real
heading prefix is zero, including when the original endpoint flag reverses local order. -/
theorem exists_oriented_original_cutBank_straight_roll (retain : Set C.Seam)
    (s : C.CutSeam retain) (side flag : Bool) :
    ∃ n : ℕ, ∃ chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain n,
      (∀ i, E.originalComplex.boundaryChainRollHeading chain i = 0) ∧
      E.originalBankEndProjection chain.first =
        ((K.projectedTriangle (C.seamSide s.val side).face).endpoint
          (C.seamSide s.val side).edge flag).val ∧
      E.originalBankEndProjection
        (E.originalComplex.boundaryTurn (E.originalRetain retain) chain.last) =
          ((K.projectedTriangle (C.seamSide s.val side).face).endpoint
            (C.seamSide s.val side).edge (!flag)).val ∧
      ∃ index : Fin (n + 1) ≃
          E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge,
        ∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (chain.point i)).1 =
          E.subdividedCutBank retain s side (index i) := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  obtain ⟨n, chain, heading, first, last, index, named⟩ :=
    E.exists_original_cutBank_straight_roll retain s side
  cases flag
  · exact ⟨n, chain, heading, first, last, index, named⟩
  · refine ⟨n, chain.reverse, D.boundaryChainRollHeading_reverse_eq_zero chain heading,
      ?_, ?_, Fin.revPerm.trans index, ?_⟩
    · simpa only [PairedInvolutions.System.Chain.reverse_first] using! last
    · have endpoint : D.boundaryTurn kept chain.reverse.last = chain.first := by
        rw [PairedInvolutions.System.Chain.reverse_last]
        exact D.boundaryTurn_involutive kept chain.first
      rw [endpoint]
      exact first
    · intro i
      change (D.boundaryEndEquiv kept (D.boundaryTurn kept (chain.point i.rev))).1 =
        E.subdividedCutBank retain s side (index i.rev)
      simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
      exact named i.rev

end Unfoldings.ConvexRoof.CompletionMesh
