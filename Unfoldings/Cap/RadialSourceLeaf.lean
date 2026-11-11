module

public import Unfoldings.Cap.CompletedRootPathSupport

/-! An interior source is a leaf of every source-distance forest, including its flat completion. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)
  {source : C.Vertex Set.univ} (at_source : K.projectedVertex source = q)

include at_source

theorem completed_nonroot_parent_ne_source (w : C.Vertex Set.univ)
    (nonroot : w ∉ R.spanningCompletion.parents.roots) :
    R.spanningCompletion.parents.parent w ≠ source := by
  intro equal
  have ascending := R.spanningCompletion.parents.ascending w nonroot
  rw [equal] at ascending
  have height := R.spanningCompletion.height_eq.trans R.height_eq
  have first := congrFun height w
  have last := congrFun height source
  rw [first, last, at_source, dist_self] at ascending
  exact (not_lt_of_ge dist_nonneg) ascending

theorem completed_parent_ne_internal_source
    (internal : ¬ C.IsBoundaryVertex Set.univ source) (w : C.Vertex Set.univ) :
    R.spanningCompletion.parents.parent w ≠ source := by
  by_cases root : w ∈ R.spanningCompletion.parents.roots
  · rw [R.spanningCompletion.parents.fixed_root w root]
    intro same
    have boundary : C.IsBoundaryVertex Set.univ w :=
      (Set.ext_iff.mp R.spanningCompletion.roots_eq w).mp root
    exact internal (same ▸ boundary)
  · exact R.completed_nonroot_parent_ne_source at_source w root

theorem completed_ancestor_source_iff
    (internal : ¬ C.IsBoundaryVertex Set.univ source) (w : C.Vertex Set.univ) :
    R.spanningCompletion.parents.Ancestor w source ↔ w = source := by
  constructor
  · rintro ⟨n, equal⟩
    cases n with
    | zero => exact equal
    | succ n =>
      rw [Function.iterate_succ_apply'] at equal
      exact (R.completed_parent_ne_internal_source at_source internal _ equal).elim
  · rintro rfl
    exact R.spanningCompletion.parents.ancestor_refl _

theorem completed_descendants_source
    (internal : ¬ C.IsBoundaryVertex Set.univ source) :
    R.spanningCompletion.parents.descendants source = {source} := by
  classical
  ext w
  simp only [R.spanningCompletion.parents.mem_descendants,
    R.completed_ancestor_source_iff at_source internal, Finset.mem_singleton]

theorem completedSubtreeCurvature_source
    (internal : ¬ C.IsBoundaryVertex Set.univ source) :
    R.completedSubtreeCurvature source = C.interiorAngularDefect Set.univ source := by
  classical
  rw [completedSubtreeCurvature, R.completed_descendants_source at_source internal,
    Finset.sum_singleton]

end Unfoldings.ConvexCap.RadialCutForest
