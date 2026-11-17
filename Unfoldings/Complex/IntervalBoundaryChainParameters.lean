module

public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Metric.ClosedIntervalLineMapEndpoints

/-! Actual boundary successors force exact increasing parameters on an embedded interval. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {T : ℝ} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)
  (lower upper : Fin (n + 1) → Set.Icc (0 : ℝ) T)
  (forward : ∀ i, lower i < upper i)
  (curve : Set.Icc (0 : ℝ) T → C.Realization retain) (injective : Function.Injective curve)
  (matching : ∀ i u, C.directedBoundaryPath (chain.point i) u = curve
    (closedNonnegativeIntervalLineMap (lower i).val (upper i).val T
      (lower i).property.1 (forward i).le (upper i).property.2 u))

include injective matching in
/-- The original boundary successor forces equality of the actual interval endpoints. -/
theorem boundaryChain_interval_joins (i : Fin n) : upper i.castSucc = lower i.succ := by
  have first := matching i.castSucc 1
  have last := matching i.succ 0
  rw [closedIntervalLineMap_one, C.directedBoundaryPath_one] at first
  rw [closedIntervalLineMap_zero, C.directedBoundaryPath_zero] at last
  have next := congrArg (C.boundaryEndVertex retain) (chain.next i)
  change C.boundaryEndVertex retain
    (C.boundaryMate retain (C.boundaryTurn retain (chain.point i.castSucc))) =
      C.boundaryEndVertex retain (chain.point i.succ) at next
  rw [(C.boundaryMate_spec retain _).2] at next
  exact injective (first.symm.trans ((congrArg (C.vertexPoint retain) next).trans last))

/-- Original bank starts, followed by the final bank's original endpoint. -/
def boundaryChainIntervalTime : Fin (n + 2) → Set.Icc (0 : ℝ) T :=
  Fin.lastCases (upper (Fin.last n)) lower

@[simp] theorem boundaryChainIntervalTime_castSucc (i : Fin (n + 1)) :
    boundaryChainIntervalTime lower upper i.castSucc = lower i :=
  Fin.lastCases_castSucc _

@[simp] theorem boundaryChainIntervalTime_last :
    boundaryChainIntervalTime lower upper (Fin.last (n + 1)) = upper (Fin.last n) :=
  Fin.lastCases_last

include injective matching in
theorem boundaryChainIntervalTime_succ (i : Fin (n + 1)) :
    boundaryChainIntervalTime lower upper i.succ = upper i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, boundaryChainIntervalTime_last]
  · rw [Fin.succ_castSucc, boundaryChainIntervalTime_castSucc,
      C.boundaryChain_interval_joins chain lower upper forward curve injective matching]

include injective matching in
/-- The actual original bank order is strictly increasing in the original interval time. -/
theorem strictMono_boundaryChainIntervalTime :
    StrictMono (boundaryChainIntervalTime lower upper) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [boundaryChainIntervalTime_castSucc,
    C.boundaryChainIntervalTime_succ chain lower upper forward curve injective matching]
  exact forward i

end Unfoldings.TriangleComplex
