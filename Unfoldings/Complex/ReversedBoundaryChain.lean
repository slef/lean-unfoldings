module

public import Unfoldings.Topology.ChainReversal
public import Unfoldings.Complex.BoundaryChainRolling

/-! Reversing actual bank traversal preserves the named internal vertex fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- Zero unreduced heading on every prefix detects the actual straight internal fan. -/
theorem boundaryChain_internal_angle_of_zero_heading
    (zero : ∀ i, C.boundaryChainRollHeading chain i = 0) (i : Fin n) :
    C.totalAngle retain (C.boundaryEndVertex retain (chain.point i.succ)) = Real.pi := by
  have step := Fin.partialSum_succ (fun k : Fin n => Real.pi -
    C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))) i
  change C.boundaryChainRollHeading chain i.succ =
    C.boundaryChainRollHeading chain i.castSucc +
      (Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point i.succ))) at step
  rw [zero, zero] at step
  linarith

/-- The reversed internal hinge is the same actual original vertex copy. -/
theorem boundaryChain_reverse_internal_angle (i : Fin n) :
    C.totalAngle retain (C.boundaryEndVertex retain (chain.reverse.point i.succ)) =
      C.totalAngle retain (C.boundaryEndVertex retain (chain.point i.rev.succ)) := by
  have step : C.boundaryMate retain (C.boundaryTurn retain (chain.point i.rev.castSucc)) =
      chain.point i.rev.succ := chain.next i.rev
  have same := (C.boundaryMate_spec retain
    (C.boundaryTurn retain (chain.point i.rev.castSucc))).2
  rw [step] at same
  change C.totalAngle retain
    (C.boundaryEndVertex retain (C.boundaryTurn retain (chain.point i.succ.rev))) = _
  rw [Fin.rev_succ]
  exact congrArg (C.totalAngle retain) same.symm

/-- A straight fine refinement has zero extra real heading in either traversal direction. -/
theorem boundaryChainRollHeading_reverse_eq_zero
    (zero : ∀ i, C.boundaryChainRollHeading chain i = 0) :
    ∀ i, C.boundaryChainRollHeading chain.reverse i = 0 := by
  apply C.boundaryChainRollHeading_eq_zero
  intro i
  rw [C.boundaryChain_reverse_internal_angle]
  exact C.boundaryChain_internal_angle_of_zero_heading chain zero i.rev

end Unfoldings.TriangleComplex
