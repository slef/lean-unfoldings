module

public import Unfoldings.Complex.BoundaryChainRolling

/-! Real heading changes at prescribed consecutive indices of actual boundary chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- The real turn formula at any two consecutive numerical bank indices. -/
theorem boundaryChainRollHeading_step_of_indices {i j : Fin (n + 1)}
    (next : j.val = i.val + 1) :
    C.boundaryChainRollHeading chain j = C.boundaryChainRollHeading chain i +
      (Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point j))) := by
  let k : Fin n := ⟨i.val, by have bound := j.isLt; omega⟩
  have left : k.castSucc = i := Fin.ext rfl
  have right : k.succ = j := Fin.ext (by dsimp [k]; omega)
  have step := Fin.partialSum_succ (fun k : Fin n =>
    Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))) k
  change C.boundaryChainRollHeading chain k.succ = C.boundaryChainRollHeading chain k.castSucc +
    (Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))) at step
  rw [left, right] at step
  exact step

end Unfoldings.TriangleComplex
