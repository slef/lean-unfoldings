module

public import Unfoldings.Cap.RadialComponentFinePath
public import Unfoldings.Cap.ProjectedSeamEndpoints
public import Unfoldings.Topology.ChildSubtrees
public import Unfoldings.Topology.ParentOrbitEnumeration

/-! Physical order along a radial component gives actual fine-forest ancestry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem selected_parent_vertex_endpoint {P : AscendingParents (C.Vertex Set.univ)}
    (S : P.EdgeSelection C.seamGraph) (e : {w : C.Vertex Set.univ // w ∉ P.roots})
    (w : C.Vertex Set.univ)
    (member : K.projectedVertex w ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (P.parent e.val))) : w = e.val ∨ w = P.parent e.val := by
  obtain ⟨b, endpoint⟩ := K.vertex_eq_seamEndpoint_of_projected_edge w (S.edge e)
    ((K.selected_parent_segment_eq_seam S e).subset member)
  rcases S.link e with ⟨first, last⟩ | ⟨first, last⟩
  · cases b
    · exact Or.inl (endpoint.trans first.symm)
    · exact Or.inr (endpoint.trans last.symm)
  · cases b
    · exact Or.inr (endpoint.trans last.symm)
    · exact Or.inl (endpoint.trans first.symm)

namespace SectorForest

variable {K} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (w z : FineC.Vertex Set.univ) (c : F.Component)
  (unattached : ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)
  (member : Q.projectedVertex w ∈ (F.componentTail c).carrier)

include lower unattached member

theorem unattached_component_nonroot_ancestor_position
    (e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (ancestor : R.spanningCompletion.parents.Ancestor w e.val) :
    Q.projectedVertex e.val ∈ (F.componentTail c).carrier := by
  let j := (R.spanningCompletion.parents.nonrootAncestorEquiv w).symm
    ⟨e.val, e.property, ancestor⟩
  have equal : R.spanningCompletion.parents.parent^[j.val] w = e.val :=
    congrArg Subtype.val ((R.spanningCompletion.parents.nonrootAncestorEquiv w).apply_symm_apply
      ⟨e.val, e.property, ancestor⟩)
  have position := M.unattached_component_completed_path_positions F covered lower R w c
    unattached member j.castSucc
  change Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val] w) ∈
    (F.componentTail c).carrier at position
  rwa [equal] at position

/-- The edge is selected from the actual fine forest and its child lies on
the same physical radial component. No chosen geometric edge is substituted. -/
theorem unattached_component_exists_incoming_edge
    (nonroot : z ∉ R.spanningCompletion.parents.roots)
    (ancestor : R.spanningCompletion.parents.Ancestor w z) (different : w ≠ z) :
    ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
      R.spanningCompletion.parents.parent e.val = z ∧
      R.spanningCompletion.parents.Ancestor w e.val ∧
      Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧
      Q.projectedVertex e.val ∈ M.extendedGeometricCuts F := by
  obtain ⟨e, ⟨parent, reaches⟩, _⟩ :=
    R.spanningCompletion.parents.exists_unique_child_ancestor nonroot ancestor different
  have position := M.unattached_component_nonroot_ancestor_position F covered lower R w c
    unattached member e reaches
  refine ⟨e, parent, reaches, position, ?_⟩
  exact (M.extendedGeometricCuts_eq_piece_union F).symm.subset
    (Set.mem_iUnion.mpr ⟨Sum.inr c, position⟩)

theorem unattached_component_nonroot_ancestor_direction
    (positive : 0 < t) (small : t < 1) (outward : R.Outward) (i : FiveSector)
    (inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i)
    (e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (ancestor : R.spanningCompletion.parents.Ancestor w e.val) :
    Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      Q.projectedVertex e.val ∈ closedFiveSector t i := by
  let data := M.radialComponentSector positive small F covered lower c unattached member i inside
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset
      (Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩)
  have directions := data.completed_parent_directions R w on_cuts (Sum.inr c) rfl member outward
  let j := (R.spanningCompletion.parents.nonrootAncestorEquiv w).symm
    ⟨e.val, e.property, ancestor⟩
  have equal : R.spanningCompletion.parents.parent^[j.val] w = e.val :=
    congrArg Subtype.val ((R.spanningCompletion.parents.nonrootAncestorEquiv w).apply_symm_apply
      ⟨e.val, e.property, ancestor⟩)
  have direction := directions j
  change Q.projectedVertex (R.spanningCompletion.parents.parent
      (R.spanningCompletion.parents.parent^[j.val] w)) -
    Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val] w) ∈
      closedFiveSector t i at direction
  rwa [equal] at direction

/-- A fine vertex found at an intermediate component position is an actual
ancestor, not merely a point on a geometrically collinear comparison path. -/
theorem unattached_component_vertex_ancestor
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i : FiveSector)
    (inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i)
    (point : Q.projectedVertex z ∈ (F.componentTail c).carrier)
    (start : ((fiveSectorFrame t positive small i).place
        (Q.projectedVertex w - K.projectedVertex origin)).re +
        ((fiveSectorFrame t positive small i).place
          (Q.projectedVertex w - K.projectedVertex origin)).im ≤
      ((fiveSectorFrame t positive small i).place
          (Q.projectedVertex z - K.projectedVertex origin)).re +
        ((fiveSectorFrame t positive small i).place
          (Q.projectedVertex z - K.projectedVertex origin)).im)
    (finish : ((fiveSectorFrame t positive small i).place
        (Q.projectedVertex z - K.projectedVertex origin)).re +
        ((fiveSectorFrame t positive small i).place
          (Q.projectedVertex z - K.projectedVertex origin)).im <
      ((fiveSectorFrame t positive small i).place
        ((F.componentTail c).tip - K.projectedVertex origin)).re +
        ((fiveSectorFrame t positive small i).place
          ((F.componentTail c).tip - K.projectedVertex origin)).im) :
    R.spanningCompletion.parents.Ancestor w z := by
  obtain ⟨j, s, equal⟩ := M.unattached_component_point_on_completed_path F covered lower R w c
    unattached member positive small outward footprint i inside point start finish
  let e := R.completedBankChain w j
  have on_edge : Q.projectedVertex z ∈ segment ℝ (Q.projectedVertex e.val)
      (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) := by
    rw [equal]
    have actual := lineMap_mem_segment ℝ ((R.completedRootPath w).vertex j.castSucc)
      ((R.completedRootPath w).vertex j.succ) s.property
    have endpoint : (R.completedRootPath w).vertex j.succ =
        Q.projectedVertex (R.spanningCompletion.parents.parent e.val) := by
      change Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val + 1] w) = _
      rw [Function.iterate_succ_apply']
      rfl
    change (R.completedRootPath w).point j s ∈ segment ℝ
      ((R.completedRootPath w).vertex j.castSucc) ((R.completedRootPath w).vertex j.succ) at actual
    have segments : segment ℝ ((R.completedRootPath w).vertex j.castSucc)
        ((R.completedRootPath w).vertex j.succ) = segment ℝ (Q.projectedVertex e.val)
          (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) := by
      rw [endpoint]
      rfl
    exact segments.subset actual
  rcases Q.selected_parent_vertex_endpoint R.spanningCompletion.selection e z on_edge with
    first | last
  · exact ⟨j.val, first.symm⟩
  · refine ⟨j.val + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact last.symm

end SectorForest
end Unfoldings.ConvexCap
