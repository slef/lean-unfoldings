module

public import Unfoldings.Complex.RestrictedCutFanAgreement
public import Unfoldings.Complex.BoundaryChainRolling

/-! Original directed bank labels preserve complete rolling across cut face restrictions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex


universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- Exchanging bank endpoints commutes with the actual original raw germ inclusion. -/
theorem includeRestrictedGerm_boundaryTurn (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam}
    (p : (C.restrictFaces U).BoundaryEnd retain) :
    C.includeRestrictedGerm U ((C.restrictFaces U).boundaryTurn retain p).val =
      C.germOfEndpoint (C.germEdge (C.includeRestrictedGerm U p.val)) (!p.val.2) := by
  obtain ⟨⟨⟨f, i⟩, b⟩, boundary⟩ := p
  cases b <;> fin_cases i <;> rfl

local instance restrictedChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (banks : ∀ i, C.includeRestrictedGerm U (c.point i).val =
    C.includeRestrictedGerm V (d.point i).val)

include banks in
open Classical in
/-- The two actual internal terminal banks select exactly the same original corner fan. -/
theorem restricted_boundary_chain_internal_angle (i : Fin n) :
    (C.restrictFaces U).totalAngle leftRetain
        ((C.restrictFaces U).boundaryEndVertex leftRetain (c.point i.succ)) =
      (C.restrictFaces V).totalAngle rightRetain
        ((C.restrictFaces V).boundaryEndVertex rightRetain (d.point i.succ)) := by
  apply C.restricted_totalAngle_eq_of_terminal_germs U V _ _ (banks i.succ)
  have left := congrArg ((C.restrictFaces U).boundaryMate leftRetain) (c.next i)
  have right := congrArg ((C.restrictFaces V).boundaryMate rightRetain) (d.next i)
  change (C.restrictFaces U).boundaryMate leftRetain
    ((C.restrictFaces U).boundaryMate leftRetain
      ((C.restrictFaces U).boundaryTurn leftRetain (c.point i.castSucc))) =
        (C.restrictFaces U).boundaryMate leftRetain (c.point i.succ) at left
  change (C.restrictFaces V).boundaryMate rightRetain
    ((C.restrictFaces V).boundaryMate rightRetain
      ((C.restrictFaces V).boundaryTurn rightRetain (d.point i.castSucc))) =
        (C.restrictFaces V).boundaryMate rightRetain (d.point i.succ) at right
  rw [(C.restrictFaces U).boundaryMate_involutive] at left
  rw [(C.restrictFaces V).boundaryMate_involutive] at right
  rw [← left, ← right, C.includeRestrictedGerm_boundaryTurn,
    C.includeRestrictedGerm_boundaryTurn]
  have same := banks i.castSucc
  exact congrArg (fun p : C.Germ => C.germOfEndpoint (C.germEdge p) (!p.2)) same

include banks in
open Classical in
/-- Actual bank lengths are inherited from the very same original triangle edge. -/
theorem restricted_boundary_chain_length (i : Fin (n + 1)) :
    (C.restrictFaces U).boundaryBankLength (c.point i) =
      (C.restrictFaces V).boundaryBankLength (d.point i) := by
  simpa only [boundaryBankLength, includeRestrictedGerm, germFarCorner] using!
    congrArg (fun p : C.Germ =>
    dist ((C.triangle p.1.1).vertex (C.germFarCorner p).2)
      ((C.triangle p.1.1).vertex p.1.2)) (banks i)

include banks in
open Classical in
/-- Every real heading prefix agrees, including full turns. -/
theorem restricted_boundary_chain_rollHeading (i : Fin (n + 1)) :
    (C.restrictFaces U).boundaryChainRollHeading c i =
      (C.restrictFaces V).boundaryChainRollHeading d i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k previous =>
    dsimp only [boundaryChainRollHeading] at previous ⊢
    rw [Fin.partialSum_succ, Fin.partialSum_succ, previous,
      C.restricted_boundary_chain_internal_angle U V c d banks]

include banks in
open Classical in
/-- The entire normalized roll agrees, preserving arclength and all hinge positions. -/
theorem restricted_boundary_chain_roll :
    (C.restrictFaces U).boundaryChainRoll c = (C.restrictFaces V).boundaryChainRoll d := by
  unfold boundaryChainRoll
  congr 1
  · funext i
    exact C.restricted_boundary_chain_length U V c d banks i
  · funext i
    exact C.restricted_boundary_chain_rollHeading U V c d banks i

end Unfoldings.TriangleComplex
