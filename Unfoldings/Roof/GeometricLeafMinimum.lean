module

public import Unfoldings.Roof.GeometricLeafAvoidance
public import Unfoldings.Geometry.SegmentLocalMinimum
public import Unfoldings.Geometry.SegmentVertices

/-! Actual geometric leaves are local radial minima of the complete prescribed cut network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_leaf_local_radial_min (leaf : F.GeometricVertex)
    (nonroot : leaf ∉ (M.geometricParents F covered positive small).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small).roots,
      M.geometricParent F covered child ≠ leaf) :
    ∀ᶠ x in 𝓝 (F.geometricPosition leaf), x ∈ M.extendedGeometricCuts F →
      dist (origin) (F.geometricPosition leaf) ≤
        dist (origin) x := by
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let P := M.geometricParents F covered positive small
  let I := {w : F.GeometricVertex // w ∉ P.roots} ⊕ F.Component
  let piece : I → Set Plane := Sum.elim
    (fun w => segment ℝ (F.geometricPosition w.val)
      (F.geometricPosition (M.geometricParent F covered w.val)))
    (fun c => {(F.componentTail c).tip})
  have cover : M.extendedGeometricCuts F = ⋃ i, piece i := by
    rw [M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered positive small]
    ext x
    constructor
    · rintro (edge | tip)
      · obtain ⟨e, member⟩ := Set.mem_iUnion.mp edge
        exact Set.mem_iUnion.mpr ⟨Sum.inl e, member⟩
      · obtain ⟨c, rfl⟩ := tip
        exact Set.mem_iUnion.mpr ⟨Sum.inr c, rfl⟩
    · intro member
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
      cases i with
      | inl e => exact Or.inl (Set.mem_iUnion.mpr ⟨e, member⟩)
      | inr c => exact Or.inr ⟨c, member.symm⟩
  have closed : ∀ i, IsClosed (piece i) := by
    intro i
    cases i with
    | inl e => exact (compact_segment _ _).isClosed
    | inr c => exact isClosed_singleton
  rw [cover]
  apply finite_closed_cover_locally_lower_bound piece closed
    (fun x => dist (origin) x) (F.geometricPosition leaf)
  intro i at_leaf x member
  cases i with
  | inl e =>
    have endpoints := M.geometric_vertex_on_parent_endpoint F covered positive small
      leaf e.val e.property at_leaf
    have equal : leaf = e.val := endpoints.resolve_right
      (fun same => childless e.val e.property same.symm)
    obtain ⟨j, first, last, _⟩ := M.geometric_parent_piece F covered positive small e.val
      e.property
    have outward := M.cutPiece_outward F positive small j
    rw [first, last] at outward
    obtain ⟨s, interval, point⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
    have bound := dist_lineMap_le_of_inner_nonneg (origin)
      (F.geometricPosition e.val) (F.geometricPosition (M.geometricParent F covered e.val))
      outward (t := 0) (s := s) le_rfl interval.1
    rw [AffineMap.lineMap_apply_zero, point] at bound
    exact equal ▸ bound
  | inr c =>
    have position : F.geometricPosition leaf = (F.componentTail c).tip := at_leaf
    have equal : leaf = Sum.inr (Sum.inr c) := F.geometricPosition_injective position
    exact (nonroot ⟨c, equal.symm⟩).elim

end Unfoldings.ConvexRoof.SectorForest
