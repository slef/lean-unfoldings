module

public import Unfoldings.Topology.ParentFrontierReach

/-! The last fresh original parent edge arrives at the constructed first processed contact. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Finite V] {P : AscendingParents V} (S : P.ParentFrontier)

/-- The actual last original vertex before the first processed contact. -/
def contactPredecessor (v : V) : V := P.parent^[S.contactTime v - 1] v

/-- A nonempty fresh branch reaches its contact by the original selected parent edge. -/
theorem parent_contactPredecessor (v : V) (nonempty : 0 < S.contactTime v) :
    P.parent (S.contactPredecessor v) = P.parent^[S.contactTime v] v := by
  change P.parent (P.parent^[S.contactTime v - 1] v) = _
  rw [← Function.iterate_succ_apply' P.parent (S.contactTime v - 1) v]
  congr 1
  omega

/-- The last incoming original vertex remains fresh, even though its parent is processed. -/
theorem contactPredecessor_not_processed (v : V) (nonempty : 0 < S.contactTime v) :
    S.contactPredecessor v ∉ S.processed :=
  S.before_contact_not_mem v (by omega)

/-- The incoming contact edge is an actual nonroot selected edge. -/
theorem contactPredecessor_nonroot (v : V) (nonempty : 0 < S.contactTime v) :
    S.contactPredecessor v ∉ P.roots :=
  fun root => S.contactPredecessor_not_processed v nonempty (S.roots root)

end Unfoldings.AscendingParents.ParentFrontier
