module

public import Unfoldings.Roof.SectorForest
public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Geometry.RadialChainPoints

/-! Every source-centered forest path stays in its own strict acute direction wedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

theorem parent_label (nonnegative : 0 ≤ t) (small : t < 1) (v : C.Vertex Set.univ) :
    K.sourceSectorLabel t origin (M.parents.parent v) = K.sourceSectorLabel t origin v := by
  by_cases root : v ∈ M.parents.roots
  · rw [M.parents.fixed_root v root]
  · have internal : ¬ C.IsBoundaryVertex Set.univ v := by
      simpa only [M.roots_eq, Set.mem_ofPred_eq] using root
    have backward : (K.projectedVertex v - origin) 0 ≤ 0 :=
      sub_nonpos.mpr (M.maximal v internal)
    have position := mem_closedThreeSector_label_of_backward nonnegative small backward
    have preserved := threeSectorLabel_add nonnegative small position (M.direction v root)
    have sum : (K.projectedVertex v - origin) +
        (K.projectedVertex (M.parents.parent v) - K.projectedVertex v) =
          K.projectedVertex (M.parents.parent v) - origin := by abel
    rw [sum] at preserved
    exact preserved

theorem iterate_label (nonnegative : 0 ≤ t) (small : t < 1) (v : C.Vertex Set.univ) (n : ℕ) :
    K.sourceSectorLabel t origin (M.parents.parent^[n] v) = K.sourceSectorLabel t origin v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', M.parent_label nonnegative small, ih]

def rootPath (v : C.Vertex Set.univ) : PolygonalChain Plane (M.parents.distanceToRoot v) where
  vertex i := K.projectedVertex (M.parents.parent^[i.val] v)

theorem rootPath_edge (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    (M.rootPath v).edge i = K.projectedVertex (M.parents.parent (M.parents.parent^[i.val] v)) -
      K.projectedVertex (M.parents.parent^[i.val] v) := by
  change K.projectedVertex (M.parents.parent^[i.val + 1] v) -
    K.projectedVertex (M.parents.parent^[i.val] v) = _
  rw [Function.iterate_succ_apply']

theorem rootPath_directions (nonnegative : 0 ≤ t) (small : t < 1) (v : C.Vertex Set.univ)
    (i : Fin (M.parents.distanceToRoot v)) :
    (M.rootPath v).edge i ∈ strictThreeSector t (K.sourceSectorLabel t origin v) := by
  rw [M.rootPath_edge]
  have direction := M.direction _ (M.parents.iterate_lt_distanceToRoot_not_mem v i.isLt)
  rwa [M.iterate_label nonnegative small] at direction

theorem rootPath_angleMonotone (positive : 0 < t) (small : t < 1) (v : C.Vertex Set.univ) :
    (M.rootPath v).AngleMonotone (threeSectorWidth t (K.sourceSectorLabel t origin v)) := by
  let i := K.sourceSectorLabel t origin v
  have banks := threeSector_banks_inner_pos positive small i
  refine ⟨threeSectorRay t i.castSucc, threeSectorRay t i.succ, ?_, ?_, le_rfl, ?_⟩
  · intro zero
    rw [zero, inner_zero_left] at banks
    exact lt_irrefl _ banks
  · intro zero
    rw [zero, inner_zero_right] at banks
    exact lt_irrefl _ banks
  · intro j
    exact inDirectionWedge_of_closedThreeSector positive.le small i
      (strictThreeSector_subset_closed _ _ (M.rootPath_directions positive.le small v j))

theorem rootPath_globallyRadiallyMonotone (positive : 0 < t) (small : t < 1)
    (v : C.Vertex Set.univ) : (M.rootPath v).GloballyRadiallyMonotone :=
  ((M.rootPath_angleMonotone positive small v).radiallyMonotone (M.rootPath v)
    (threeSectorWidth_lt_pi_div_two positive small _).le).globallyRadiallyMonotone

/-- Each positive-length step follows an actual selected original seam. -/
theorem rootPath_original_edge (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    ∃ s : C.Seam, C.seamGraph.IsLink s (M.parents.parent^[i.val] v)
      (M.parents.parent^[i.val + 1] v) := by
  let source : {w : C.Vertex Set.univ // w ∉ M.parents.roots} :=
    ⟨M.parents.parent^[i.val] v, M.parents.iterate_lt_distanceToRoot_not_mem v i.isLt⟩
  refine ⟨M.selection.edge source, ?_⟩
  rw [Function.iterate_succ_apply']
  exact M.selection.link source

end Unfoldings.ConvexRoof.SectorForest
