module

public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Topology.ParentFrontierReach

/-! The actual finite parent path with its first root and original ordered vertex labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V) (vertex : V)

/-- Keep every original ancestor up to and including the first actual root. -/
def rootwardVertexPath : Fin (P.distanceToRoot vertex + 1) → V :=
  fun i => P.parent^[i.val] vertex

@[simp] theorem rootwardVertexPath_zero : P.rootwardVertexPath vertex 0 = vertex := rfl

@[simp] theorem rootwardVertexPath_last :
    P.rootwardVertexPath vertex (Fin.last (P.distanceToRoot vertex)) = P.root vertex :=
  P.iterate_distanceToRoot_eq_root vertex

/-- Earlier labels are ancestors of all later labels in the actual original parent order. -/
theorem rootwardVertexPath_ancestor (i j : Fin (P.distanceToRoot vertex + 1))
    (ordered : i ≤ j) :
    P.Ancestor (P.rootwardVertexPath vertex i) (P.rootwardVertexPath vertex j) := by
  refine ⟨j.val - i.val, ?_⟩
  change P.parent^[j.val - i.val] (P.parent^[i.val] vertex) = P.parent^[j.val] vertex
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel ordered]

/-- Every finite outgoing path bank starts strictly before the root. -/
theorem rootwardVertexPath_nonroot (i : Fin (P.distanceToRoot vertex)) :
    P.rootwardVertexPath vertex i.castSucc ∉ P.roots :=
  P.iterate_lt_distanceToRoot_not_mem vertex i.isLt

/-- Ancestor closure retains every original rootward path vertex in the current frontier. -/
theorem rootwardVertexPath_processed (frontier : P.ParentFrontier)
    (processed : vertex ∈ frontier.processed) (i : Fin (P.distanceToRoot vertex + 1)) :
    P.rootwardVertexPath vertex i ∈ frontier.processed :=
  frontier.iterate_mem_of_mem processed i.val

end Unfoldings.AscendingParents
