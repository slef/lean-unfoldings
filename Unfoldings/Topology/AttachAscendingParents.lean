module

public import Unfoldings.Topology.AscendingForest

/-! Attach increasing parent forests at their original roots using one shared potential. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V) (Q : AscendingParents {v // v ∈ P.roots})
  (height : ∀ v, Q.height v = P.height v.val)

open Classical in
/-- Each old root follows its new forest; every old nonroot keeps its original parent. -/
def attach : AscendingParents V where
  roots := {v | ∃ root : v ∈ P.roots,
    (⟨v, root⟩ : {v // v ∈ P.roots}) ∈ Q.roots}
  parent v := if root : v ∈ P.roots then (Q.parent ⟨v, root⟩).val else P.parent v
  height := P.height
  fixed_root v member := by
    obtain ⟨root, terminal⟩ := member
    rw [dite_eq_left root, Q.fixed_root ⟨v, root⟩ terminal]
  ascending v nonroot := by
    by_cases root : v ∈ P.roots
    · rw [dite_eq_left root]
      have not_terminal : (⟨v, root⟩ : {v // v ∈ P.roots}) ∉ Q.roots :=
        fun terminal => nonroot ⟨root, terminal⟩
      have strict := Q.ascending ⟨v, root⟩ not_terminal
      rwa [height, height] at strict
    · rw [dite_eq_right root]
      exact P.ascending v root

@[simp] theorem attach_parent_nonroot {v : V} (nonroot : v ∉ P.roots) :
    (P.attach Q height).parent v = P.parent v := by
  classical
  exact dite_eq_right nonroot

@[simp] theorem attach_parent_root (v : {v // v ∈ P.roots}) :
    (P.attach Q height).parent v.val = (Q.parent v).val := by
  classical
  exact dite_eq_left v.property

theorem attach_rootedForest [Finite V] :
    (P.attach Q height).graph.IsRootedForest (P.attach Q height).roots :=
  (P.attach Q height).graph_rootedForest

end Unfoldings.AscendingParents
