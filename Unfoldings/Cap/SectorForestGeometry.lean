module

public import Unfoldings.Cap.SectorForestPaths
public import Unfoldings.Geometry.CyclicRays

/-! Source-centered path positions, rim endpoints, and the empty forward gap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

theorem iterate_position (nonnegative : 0 ≤ t) (small : t < 1) (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) (n : ℕ) :
    K.projectedVertex (M.parents.parent^[n] v) - K.projectedVertex origin ∈
      closedThreeSector t (K.sourceSectorLabel t origin v) := by
  induction n with
  | zero =>
    exact mem_closedThreeSector_label_of_backward nonnegative small
      (sub_nonpos.mpr (M.maximal v internal))
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : M.parents.parent^[n] v ∈ M.parents.roots
    · rwa [M.parents.fixed_root _ root]
    · have direction := M.direction _ root
      rw [M.iterate_label nonnegative small] at direction
      have next := strictThreeSector_subset_closed _ _ (add_mem_strictThreeSector ih direction)
      have sum : (K.projectedVertex (M.parents.parent^[n] v) - K.projectedVertex origin) +
          (K.projectedVertex (M.parents.parent (M.parents.parent^[n] v)) -
            K.projectedVertex (M.parents.parent^[n] v)) =
          K.projectedVertex (M.parents.parent (M.parents.parent^[n] v)) -
            K.projectedVertex origin := by abel
      rwa [sum] at next

theorem rootPath_position (nonnegative : 0 ≤ t) (small : t < 1) (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) (i : Fin (M.parents.distanceToRoot v + 1)) :
    (M.rootPath v).vertex i - K.projectedVertex origin ∈
      closedThreeSector t (K.sourceSectorLabel t origin v) :=
  M.iterate_position nonnegative small v internal i.val

theorem rootPath_end (v : C.Vertex Set.univ) :
    (M.rootPath v).vertex (Fin.last (M.parents.distanceToRoot v)) =
      K.projectedVertex (M.parents.root v) :=
  congrArg K.projectedVertex (M.parents.iterate_distanceToRoot_eq_root v)

theorem rootPath_end_boundary (v : C.Vertex Set.univ) :
    C.IsBoundaryVertex Set.univ (M.parents.root v) := by
  have root := M.parents.root_mem v
  rwa [M.roots_eq] at root

include M in
/-- No other internal vertex occurs in the entire forward open halfplane at the chosen source. -/
theorem forward_gap_empty (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    ¬ 0 < (K.projectedVertex v - K.projectedVertex origin) 0 := by
  exact not_lt_of_ge (sub_nonpos.mpr (M.maximal v internal))

include M in
/-- The open gap between the three sectors contains no internal cap vertex. -/
theorem outer_sector_gap_empty (small : t < 1) (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    K.projectedVertex v - K.projectedVertex origin ∉
      strictRayCone (threeSectorRay t 3) (threeSectorRay t 0) := by
  rintro ⟨a, ha, b, hb, equal⟩
  have first := congrArg (fun z : Plane => z 0) equal
  change (K.projectedVertex v - K.projectedVertex origin) 0 =
    a * (1 - t) + b * (1 - t) at first
  have positive := add_pos (mul_pos ha (by linarith : 0 < 1 - t))
    (mul_pos hb (by linarith : 0 < 1 - t))
  apply M.forward_gap_empty v internal
  rw [first]
  exact positive

end Unfoldings.ConvexCap.SectorForest
