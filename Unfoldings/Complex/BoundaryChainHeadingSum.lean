module

public import Unfoldings.Complex.BoundaryChainRolling
public import Unfoldings.Topology.FinitePrefixSum

/-! The terminal real heading counts each bank's starting turn except the initial one. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

theorem boundaryChainRollHeading_last_eq_sum_starting_turns :
    C.boundaryChainRollHeading chain (Fin.last n) =
      (∑ i : Fin (n + 1), (Real.pi - C.totalAngle retain
        (C.boundaryEndVertex retain (chain.point i)))) -
      (Real.pi - C.totalAngle retain (C.boundaryEndVertex retain chain.first)) := by
  have heading : C.boundaryChainRollHeading chain (Fin.last n) =
      ∑ k : Fin n, (Real.pi - C.totalAngle retain
        (C.boundaryEndVertex retain (chain.point k.succ))) :=
    fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)
  rw [heading, Fin.sum_univ_succ]
  dsimp only [PairedInvolutions.System.Chain.first]
  ring

end Unfoldings.TriangleComplex
