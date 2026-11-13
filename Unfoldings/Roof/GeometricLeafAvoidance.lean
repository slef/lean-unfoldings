module

public import Unfoldings.Roof.GeometricCutIncidence
public import Unfoldings.Topology.ChildlessAncestors

/-! An unprocessed geometric leaf cannot lie on another leaf's existing root path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

/-- Incidence plus childlessness rules out contacts anywhere on another original parent path. -/
theorem geometric_leaf_eq_of_mem_ancestor_edge (leaf z w : F.GeometricVertex)
    (leaf_nonroot : leaf ∉ (M.geometricParents F covered positive small).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small).roots,
      M.geometricParent F covered child ≠ leaf)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots)
    (ancestor : (M.geometricParents F covered positive small).Ancestor z w)
    (member : F.geometricPosition leaf ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))) : z = leaf := by
  let P := M.geometricParents F covered positive small
  have endpoint := M.geometric_vertex_on_parent_endpoint F covered positive small leaf w
    nonroot member
  have reaches : P.Ancestor z leaf := by
    rcases endpoint with first | last
    · exact first.symm ▸ ancestor
    · exact ancestor.trans P ⟨1, last.symm⟩
  exact (P.ancestor_childless_iff leaf_nonroot childless z).mp reaches

/-- Source distance is nonnegative, so no increasing geometric parent can enter the source. -/
theorem geometric_origin_childless (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots) :
    F.geometricPosition (M.geometricParent F covered w) ≠ origin := by
  let P := M.geometricParents F covered positive small
  intro same
  have ascending := P.ascending w nonroot
  change dist (origin) (F.geometricPosition w) <
    dist (origin) (F.geometricPosition (M.geometricParent F covered w))
      at ascending
  rw [same] at ascending
  rw [dist_self] at ascending
  exact not_lt_of_ge dist_nonneg ascending

end Unfoldings.ConvexRoof.SectorForest
