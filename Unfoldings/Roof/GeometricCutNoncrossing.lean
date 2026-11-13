module

public import Unfoldings.Roof.GeometricCutIncidence

/-! Distinct edges of the complete geometric forest meet only at shared endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))

theorem cutPiece_eq_of_regular_intersection
    (a b : M.ExtendedCutPiece F) {x : Plane}
    (first : x ∈ segment ℝ (M.cutPieceFirst F a) (M.cutPieceLast F a))
    (last : x ∈ segment ℝ (M.cutPieceFirst F b) (M.cutPieceLast F b))
    (regular : ∀ w : F.GeometricVertex, x ≠ F.geometricPosition w) : a = b := by
  have old_skirt (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) (c : F.Component)
      (old : x ∈ segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (M.parents.parent e.val)))
      (skirt : x ∈ (F.componentTail c).carrier) : False := by
    have member := K.convex_projection.segment_subset (K.projectedVertex_mem_footprint e.val)
      (K.projectedVertex_mem_footprint (M.parents.parent e.val)) old
    have rim := (mem_frontier_iff_notMem_interior member).mpr (F.component_outside c skirt)
    exact regular (Sum.inl (M.parents.parent e.val)) (M.parent_segment_frontier_endpoint e old rim)
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have point_regular (f : Face) (j : Fin 3) : x ≠ (K.projectedTriangle f).vertex j := by
        exact regular (Sum.inl (C.vertexOfCorner Set.univ (f, j)))
      have seams := K.projected_seam_unique_at_regular_point (M.selection.edge a)
        (M.selection.edge b) ((M.parent_segment_eq_original_seam a).subset first)
        ((M.parent_segment_eq_original_seam b).subset last) point_regular
      exact congrArg Sum.inl (M.selection.edge_injective seams)
    | inr b => exact (old_skirt a b first last).elim
  | inr a =>
    cases b with
    | inl b => exact (old_skirt b a last first).elim
    | inr b => exact congrArg Sum.inr (F.component_eq_of_common_mem a b first last)

variable (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
  K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_parent_eq_of_regular_intersection (a b : F.GeometricVertex)
    (first_nonroot : a ∉ (M.geometricParents F covered positive small).roots)
    (last_nonroot : b ∉ (M.geometricParents F covered positive small).roots) {x : Plane}
    (first : x ∈ segment ℝ (F.geometricPosition a)
      (F.geometricPosition (M.geometricParent F covered a)))
    (last : x ∈ segment ℝ (F.geometricPosition b)
      (F.geometricPosition (M.geometricParent F covered b)))
    (regular : ∀ w : F.GeometricVertex, x ≠ F.geometricPosition w) : a = b := by
  obtain ⟨i, first_start, first_finish, _⟩ :=
    M.geometric_parent_piece F covered positive small a first_nonroot
  obtain ⟨j, last_start, last_finish, _⟩ :=
    M.geometric_parent_piece F covered positive small b last_nonroot
  have first_piece : x ∈ segment ℝ (M.cutPieceFirst F i) (M.cutPieceLast F i) := by
    rwa [first_start, first_finish]
  have last_piece : x ∈ segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j) := by
    rwa [last_start, last_finish]
  have same := M.cutPiece_eq_of_regular_intersection F i j first_piece last_piece regular
  exact F.geometricPosition_injective
    (first_start.symm.trans ((congrArg (M.cutPieceFirst F) same).trans last_start))

/-- Distinct projected cut edges meet only at shared endpoints.
This does not assert nonoverlap of their developments. -/
theorem geometric_parent_intersection_endpoints (a b : F.GeometricVertex) (different : a ≠ b)
    (first_nonroot : a ∉ (M.geometricParents F covered positive small).roots)
    (last_nonroot : b ∉ (M.geometricParents F covered positive small).roots) {x : Plane}
    (first : x ∈ segment ℝ (F.geometricPosition a)
      (F.geometricPosition (M.geometricParent F covered a)))
    (last : x ∈ segment ℝ (F.geometricPosition b)
      (F.geometricPosition (M.geometricParent F covered b))) :
    (x = F.geometricPosition a ∨ x = F.geometricPosition (M.geometricParent F covered a)) ∧
      (x = F.geometricPosition b ∨ x = F.geometricPosition (M.geometricParent F covered b)) := by
  by_cases vertex : ∃ w : F.GeometricVertex, F.geometricPosition w = x
  · obtain ⟨w, rfl⟩ := vertex
    constructor
    · exact (M.geometric_vertex_on_parent_endpoint F covered positive small w a
        first_nonroot first).imp (congrArg F.geometricPosition) (congrArg F.geometricPosition)
    · exact (M.geometric_vertex_on_parent_endpoint F covered positive small w b
        last_nonroot last).imp (congrArg F.geometricPosition) (congrArg F.geometricPosition)
  · have regular : ∀ w : F.GeometricVertex, x ≠ F.geometricPosition w :=
      fun w equal => vertex ⟨w, equal.symm⟩
    exact (different (M.geometric_parent_eq_of_regular_intersection F covered positive small
      a b first_nonroot last_nonroot first last regular)).elim

end Unfoldings.ConvexRoof.SectorForest
