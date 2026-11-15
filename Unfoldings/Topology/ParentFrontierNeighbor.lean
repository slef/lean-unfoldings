module

public import Unfoldings.Topology.ParentFrontierReach

/-! A fresh original neighbor of a processed vertex reaches the frontier in one parent step. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Finite V] {P : AscendingParents V} (S : P.ParentFrontier)

omit [Finite V] in
/-- A fresh adjacent original forest vertex can only be a child of its processed neighbor. -/
theorem parent_eq_of_fresh_neighbor {previous vertex : V}
    (processed : previous ∈ S.processed) (fresh : vertex ∉ S.processed)
    (neighbors : P.parent vertex = previous ∨ P.parent previous = vertex ∨
      (previous ∈ P.roots ∧ vertex ∈ P.roots)) : P.parent vertex = previous := by
  rcases neighbors with forward | backward | both_roots
  · exact forward
  · exact (fresh (backward ▸ S.closed previous processed)).elim
  · exact (fresh (S.roots both_roots.2)).elim

/-- In an original neighbor traversal, every new source after the first has a singleton
fresh branch; its parent is already on the actual processed frontier. -/
theorem contactTime_eq_one_of_fresh_neighbor {previous vertex : V}
    (processed : previous ∈ S.processed) (fresh : vertex ∉ S.processed)
    (neighbors : P.parent vertex = previous ∨ P.parent previous = vertex ∨
      (previous ∈ P.roots ∧ vertex ∈ P.roots)) : S.contactTime vertex = 1 := by
  have parent := S.parent_eq_of_fresh_neighbor processed fresh neighbors
  have after : P.parent^[1] vertex ∈ S.processed := by simpa only [Function.iterate_one, parent]
  have upper := (S.contactTime_le_iff vertex 1).mpr after
  have not_zero : S.contactTime vertex ≠ 0 := fun zero =>
    fresh ((S.contactTime_eq_zero_iff vertex).mp zero)
  omega

/-- Prefix processing uses exactly the actual next seed of the original ordered list. -/
theorem run_take_succ (seeds : List V) (i : Fin seeds.length) :
    S.run (seeds.take (i.val + 1)) = (S.run (seeds.take i.val)).process seeds[i.val] := by
  have split : seeds.take (i.val + 1) = seeds.take i.val ++ [seeds[i.val]] :=
    (List.take_concat_get' seeds i.val i.isLt).symm
  rw [split]
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A singleton first-contact branch adds precisely its original source vertex. -/
theorem process_processed_eq_insert {vertex : V} (single : S.contactTime vertex = 1) :
    (S.process vertex).processed = insert vertex S.processed := by
  change S.processed ∪ Set.range (fun i : Fin (S.contactTime vertex) =>
    P.parent^[i.val] vertex) = _
  rw [single]
  have range_eq : Set.range (fun i : Fin 1 => P.parent^[i.val] vertex) = {vertex} := by
    ext w
    constructor
    · rintro ⟨i, equal⟩
      have zero : i.val = 0 := by omega
      exact Set.mem_singleton_iff.mpr (by
        simpa only [zero, Function.iterate_zero_apply] using equal.symm)
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [range_eq, Set.union_comm]
  rfl

end Unfoldings.AscendingParents.ParentFrontier
