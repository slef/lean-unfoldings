module

public import Unfoldings.Basic
public import Unfoldings.Topology.PathFrontier
public import Mathlib.Analysis.Convex.Basic

/-! Convex sets cannot escape an open region without crossing its frontier. -/

@[expose] public section

namespace Unfoldings

/-- A convex set meeting the interior and avoiding the frontier stays entirely inside. -/
theorem convex_subset_interior_of_avoids_frontier {S K : Set Plane} (convex : Convex ℝ S)
    (closed : IsClosed K) {a : Plane} (member : a ∈ S) (inside : a ∈ interior K)
    (avoids : Disjoint S (frontier K)) : S ⊆ interior K := by
  intro b hb
  by_cases in_K : b ∈ K
  · by_contra outside
    exact Set.disjoint_left.mp avoids hb ⟨subset_closure in_K, outside⟩
  · let path (t : unitInterval) : Plane := (1 - (t : ℝ)) • a + (t : ℝ) • b
    have continuous : Continuous path := by dsimp [path]; fun_prop
    have first : path 0 = a := by simp [path]
    have last : path 1 = b := by simp [path]
    obtain ⟨t, _positive, _before, boundary⟩ := exists_inner_time_mem_frontier closed path
      continuous (first.symm ▸ inside) (last.symm ▸ in_K)
    have along : path t ∈ S :=
      convex member hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    exact (Set.disjoint_left.mp avoids along boundary).elim

end Unfoldings
