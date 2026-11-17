module

public import Unfoldings.Complex.BoundaryChainPath
public import Unfoldings.Complex.IntervalBoundaryChainParameters
public import Unfoldings.Metric.PositiveClosedInterval

/-! Exact interval-bank matching determines the actual chain's parameter order and joins. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)
  {T : ℝ} (lower upper : Fin (n + 1) → Set.Icc (0 : ℝ) T)
  (forward : ∀ i, (lower i).val < (upper i).val)
  (curve : Set.Icc (0 : ℝ) T → C.Realization retain)
  (matching : ∀ i u, C.directedBoundaryPath (chain.point i) u =
    curve (closedNonnegativeIntervalLineMap (lower i).val (upper i).val T
      (lower i).property.1 (forward i).le (upper i).property.2 u))

include matching in
/-- The original beginning of each directed bank has its exact lower interval time. -/
theorem boundaryChain_interval_first (i : Fin (n + 1)) :
    C.vertexPoint retain (C.boundaryEndVertex retain (chain.point i)) = curve (lower i) := by
  have first := matching i 0
  rw [C.directedBoundaryPath_zero] at first
  apply first.trans
  apply congrArg curve
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap, Set.Icc.coe_zero,
    zero_mul, add_zero]

include matching in
/-- The original finish of each directed bank has its exact upper interval time. -/
theorem boundaryChain_interval_last (i : Fin (n + 1)) :
    C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain (chain.point i))) =
      curve (upper i) := by
  have last := matching i 1
  rw [C.directedBoundaryPath_one] at last
  apply last.trans
  apply congrArg curve
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap, Set.Icc.coe_one,
    one_mul, add_sub_cancel]

variable (injective : Function.Injective curve)

include matching injective in
/-- An embedded forward interval chain automatically has strictly ordered start times. -/
theorem boundaryChain_interval_strictMono : StrictMono (fun i => (lower i).val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have same := congrArg Subtype.val
    (C.boundaryChain_interval_joins chain lower upper forward curve injective matching i)
  exact (forward i.castSucc).trans_eq same

include matching injective in
/-- Every genuine internal hinge is strictly between the interval's two endpoints. -/
theorem boundaryChain_interval_internal (i : Fin n) :
    0 < (lower i.succ).val ∧ (lower i.succ).val < T := by
  have same := congrArg Subtype.val
    (C.boundaryChain_interval_joins chain lower upper forward curve injective matching i)
  exact ⟨(lower i.castSucc).property.1.trans_lt ((forward i.castSucc).trans_eq same),
    (forward i.succ).trans_le (upper i.succ).property.2⟩

end Unfoldings.TriangleComplex
