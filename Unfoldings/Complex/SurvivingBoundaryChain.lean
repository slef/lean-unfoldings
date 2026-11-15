module

public import Unfoldings.Complex.SurvivingBoundaryBanks
public import Unfoldings.Complex.RestoredLinkChain
public import Unfoldings.Complex.BoundaryChainRolling

/-! Restore side cuts along a surviving directed bank chain without changing its intrinsic rolls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (c : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (c.point i).val))

include inclusion in
/-- Keep all original bank tags and restore only the cuts outside this actual chain. -/
def survivingBoundaryChain : (C.boundarySystem large).Chain n where
  point i := C.survivingBoundaryEnd (c.point i) (survives i)
  injective := by
    intro i j same
    exact c.injective (Subtype.ext (congrArg (fun p : C.BoundaryEnd large => p.val) same))
  disjoint i j same := c.disjoint i j
    (Subtype.ext (congrArg (fun p : C.BoundaryEnd large => p.val) same))
  next := by
    intro i
    let p := C.boundaryTurn large (C.survivingBoundaryEnd (c.point i.castSucc) (survives _))
    let q := C.survivingBoundaryEnd (c.point i.succ) (survives _)
    have current := congrArg (C.boundaryEndVertex small) (c.next i)
    change C.boundaryEndVertex small
      (C.boundaryMate small (C.boundaryTurn small (c.point i.castSucc))) =
        C.boundaryEndVertex small (c.point i.succ) at current
    have same : C.boundaryEndVertex large q = C.boundaryEndVertex large p := by
      change C.vertexForgetCuts inclusion (C.boundaryEndVertex small (c.point i.succ)) =
        C.vertexForgetCuts inclusion
          (C.boundaryEndVertex small (C.boundaryTurn small (c.point i.castSucc)))
      rw [← current, (C.boundaryMate_spec small _).2]
    have different : q ≠ p := by
      intro equal
      exact c.disjoint i.succ i.castSucc
        (Subtype.ext (congrArg (fun p : C.BoundaryEnd large => p.val) equal))
    exact ((C.exists_unique_other_boundaryEnd large p).unique ⟨different, same⟩
      (C.boundaryMate_spec large p)).symm

/-- Each internal fan's whole original angle survives. -/
theorem survivingBoundaryChain_internal_angle (i : Fin n) :
    C.totalAngle large (C.boundaryEndVertex large
      ((C.survivingBoundaryChain inclusion c survives).point i.succ)) =
      C.totalAngle small (C.boundaryEndVertex small (c.point i.succ)) := by
  have mate := congrArg (C.boundaryMate small) (c.next i)
  change C.boundaryMate small (C.boundaryMate small
    (C.boundaryTurn small (c.point i.castSucc))) =
      C.boundaryMate small (c.point i.succ) at mate
  rw [C.boundaryMate_involutive] at mate
  have last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate small (c.point i.succ)).val) := by
    rw [← mate]
    have raw := congrArg (fun bank : C.BoundaryBank small => bank.val)
      ((C.boundaryEnd_bank_eq_iff small (C.boundaryTurn small (c.point i.castSucc))
        (c.point i.castSucc)).mpr (Or.inr rfl))
    change C.germEdge _ = C.germEdge _ at raw
    rw [raw]
    exact survives i.castSucc
  exact C.boundary_fan_totalAngle inclusion (c.point i.succ) (survives _) last

/-- All unreduced heading prefixes are identical, rather than merely equal modulo a full turn. -/
theorem survivingBoundaryChain_rollHeading (i : Fin (n + 1)) :
    C.boundaryChainRollHeading (C.survivingBoundaryChain inclusion c survives) i =
      C.boundaryChainRollHeading c i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k ih =>
    dsimp only [boundaryChainRollHeading] at ih ⊢
    rw [Fin.partialSum_succ, Fin.partialSum_succ, ih,
      C.survivingBoundaryChain_internal_angle]

/-- The complete normalized polygonal bank rolls agree, including all original lengths
and all hinge positions accumulated from those lengths and real headings. -/
theorem survivingBoundaryChain_roll :
    C.boundaryChainRoll (C.survivingBoundaryChain inclusion c survives) =
      C.boundaryChainRoll c := by
  unfold boundaryChainRoll
  congr 1
  funext i
  exact C.survivingBoundaryChain_rollHeading inclusion c survives i

end Unfoldings.TriangleComplex
