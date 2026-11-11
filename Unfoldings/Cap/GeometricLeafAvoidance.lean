module

public import Unfoldings.Cap.GeometricCutIncidence
public import Unfoldings.Topology.ChildlessAncestors

/-! An unprocessed geometric leaf cannot lie on another leaf's existing root path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

/-- Incidence plus childlessness rules out contacts anywhere on another original parent path. -/
theorem geometric_leaf_eq_of_mem_ancestor_edge (leaf z w : F.GeometricVertex)
    (leaf_nonroot : leaf ∉ (M.geometricParents F covered positive small lower).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small lower).roots,
      M.geometricParent F covered child ≠ leaf)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
    (ancestor : (M.geometricParents F covered positive small lower).Ancestor z w)
    (member : F.geometricPosition leaf ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))) : z = leaf := by
  let P := M.geometricParents F covered positive small lower
  have endpoint := M.geometric_vertex_on_parent_endpoint F covered positive small lower leaf w
    nonroot member
  have reaches : P.Ancestor z leaf := by
    rcases endpoint with first | last
    · exact first.symm ▸ ancestor
    · exact ancestor.trans P ⟨1, last.symm⟩
  exact (P.ancestor_childless_iff leaf_nonroot childless z).mp reaches

/-- Source distance is nonnegative, so no increasing geometric parent can enter the source. -/
theorem geometric_origin_childless (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots) :
    M.geometricParent F covered w ≠ Sum.inl origin := by
  let P := M.geometricParents F covered positive small lower
  intro same
  have ascending := P.ascending w nonroot
  change dist (K.projectedVertex origin) (F.geometricPosition w) <
    dist (K.projectedVertex origin) (F.geometricPosition (M.geometricParent F covered w))
      at ascending
  rw [same] at ascending
  change dist (K.projectedVertex origin) (F.geometricPosition w) <
    dist (K.projectedVertex origin) (K.projectedVertex origin) at ascending
  rw [dist_self] at ascending
  exact not_lt_of_ge dist_nonneg ascending

end Unfoldings.ConvexCap.SectorForest
