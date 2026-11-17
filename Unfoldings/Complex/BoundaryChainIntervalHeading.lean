module

public import Unfoldings.Topology.ChainInterval
public import Unfoldings.Complex.BoundaryChainHeadingStep

/-! Consecutive actual bank windows retain exact differences of unreduced real headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- Rolling a consecutive window subtracts precisely its original initial real heading.
No orientation, flatness or injectivity of the developed image is assumed. -/
theorem boundaryChainRollHeading_interval (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) :
    C.boundaryChainRollHeading (chain.interval first length fits) i =
      C.boundaryChainRollHeading chain (chain.intervalIndex first length fits i) -
        C.boundaryChainRollHeading chain (chain.intervalIndex first length fits 0) := by
  induction i using Fin.induction with
  | zero => exact (sub_self _).symm
  | succ k previous =>
    have small := C.boundaryChainRollHeading_step_of_indices (chain.interval first length fits)
      (i := k.castSucc) (j := k.succ) rfl
    have big := C.boundaryChainRollHeading_step_of_indices chain
      (i := chain.intervalIndex first length fits k.castSucc)
      (j := chain.intervalIndex first length fits k.succ) (by
        change first + (k.val + 1) = first + k.val + 1
        omega)
    rw [small, previous, big, PairedInvolutions.System.Chain.interval_point]
    ring

end Unfoldings.TriangleComplex
