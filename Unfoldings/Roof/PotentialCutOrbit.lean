module

public import Unfoldings.Roof.PotentialCutDisk
public import Unfoldings.Topology.ParentPaths

/-! Nontrivial selected parent orbits end on the actual rim, never at unused flat roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)

/-- The far endpoint of every actual selected parent seam is on the prescribed cuts. -/
theorem parent_mem_cuts (v : C.Vertex Set.univ) (nonroot : v ∉ R.parents.roots) :
    K.projectedVertex (R.parents.parent v) ∈ cuts := by
  let e : {v // v ∉ R.parents.roots} := ⟨v, nonroot⟩
  let s := R.selection.edge e
  apply R.selected_subset e
  rcases R.selection.link e with ⟨_, last⟩ | ⟨_, last⟩
  · change R.parents.parent v = C.seamVertex s true at last
    rw [last]
    exact right_mem_segment ℝ _ _
  · change R.parents.parent v = C.seamVertex s false at last
    rw [last]
    exact left_mem_segment ℝ _ _

/-- An orbit that contains an edge reaches a used root on the actual cut geometry. -/
theorem root_mem_cuts (v : C.Vertex Set.univ) (nontrivial : 0 < R.parents.distanceToRoot v) :
    K.projectedVertex (R.parents.root v) ∈ cuts := by
  let k := R.parents.distanceToRoot v - 1
  have before : k < R.parents.distanceToRoot v := by dsimp [k]; omega
  have selected := R.parent_mem_cuts _ (R.parents.iterate_lt_distanceToRoot_not_mem v before)
  have next : k.succ = R.parents.distanceToRoot v := by dsimp [k]; omega
  rw [← Function.iterate_succ_apply' R.parents.parent k v, next,
    R.parents.iterate_distanceToRoot_eq_root] at selected
  exact selected

/-- Unused isolated flat roots are never the end of an actual nonempty selected path. -/
theorem root_isBoundaryVertex (v : C.Vertex Set.univ)
    (nontrivial : 0 < R.parents.distanceToRoot v) :
    C.IsBoundaryVertex Set.univ (R.parents.root v) := by
  rcases (Set.ext_iff.mp R.roots_eq _).mp (R.parents.root_mem v) with rim | unused
  · exact rim
  · exact (unused (R.root_mem_cuts v nontrivial)).elim

end Unfoldings.ConvexRoof.PotentialCutForest
