module

public import Unfoldings.Geometry.ChainInterval
public import Unfoldings.Geometry.ChainPaths

/-! Split actual polygonal chain carriers at any original vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

theorem point_mem_path_range (i : Fin n) (t : unitInterval) : P.point i t ∈ Set.range P.path := by
  rw [P.path_range]
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩)

theorem vertex_mem_path_range (i : Fin (n + 1)) : P.vertex i ∈ Set.range P.path := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨0, P.path.source⟩
  · simpa only [P.point_one] using P.point_mem_path_range j 1

theorem interval_path_range_subset (first length : ℕ) (fits : first + length ≤ n) :
    Set.range (P.interval first length fits).path ⊆ Set.range P.path := by
  intro z hz
  have cover := (P.interval first length fits).path_range.subset hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
  rcases cover with initial | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp initial]
    exact P.vertex_mem_path_range ⟨first, by omega⟩
  · rw [P.interval_point]
    exact P.point_mem_path_range _ _

/-- Shared split endpoints are retained on both sides, even if adjacent edges collapse. -/
theorem path_range_split (hinge : Fin (n + 1)) :
    Set.range P.path =
      Set.range (P.interval 0 hinge.val (by omega)).path ∪
        Set.range (P.interval hinge.val (n - hinge.val) (by omega)).path := by
  let A := P.interval 0 hinge.val (by omega)
  let B := P.interval hinge.val (n - hinge.val) (by omega)
  apply Set.Subset.antisymm
  · intro z hz
    have cover := P.path_range.subset hz
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
    rcases cover with initial | ⟨i, t, rfl⟩
    · left
      rw [Set.mem_singleton_iff.mp initial]
      exact A.vertex_mem_path_range 0
    · by_cases before : i.val < hinge.val
      · left
        let j : Fin hinge.val := ⟨i.val, before⟩
        have same : A.point j t = P.point i t := by
          rw [interval_point]
          congr 1
          apply Fin.ext
          simp only [Nat.zero_add]
          rfl
        rw [← same]
        exact A.point_mem_path_range j t
      · right
        let j : Fin (n - hinge.val) := ⟨i.val - hinge.val, by omega⟩
        have index : (⟨hinge.val + j.val, by omega⟩ : Fin n) = i := Fin.ext (by dsimp [j]; omega)
        have same : B.point j t = P.point i t := by
          rw [interval_point, index]
        rw [← same]
        exact B.point_mem_path_range j t
  · exact Set.union_subset (P.interval_path_range_subset _ _ _)
      (P.interval_path_range_subset _ _ _)

end Unfoldings.PolygonalChain
