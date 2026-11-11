module

public import Unfoldings.Cap.GeometricCutNoncrossing

/-! The complete geometric cut forest has a unique forward edge at every nonterminal point. -/

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

/-- Incoming edges omit their parent endpoint; the unique outgoing edge includes its child.
This convention resolves branching vertices without identifying their developed bank copies. -/
theorem geometric_halfOpen_parent_unique
    (a b : {w : F.GeometricVertex //
      w ∉ (M.geometricParents F covered positive small lower).roots}) {x : Plane}
    (first : x ∈ segment ℝ (F.geometricPosition a.val)
      (F.geometricPosition (M.geometricParent F covered a.val)))
    (first_not_end : x ≠ F.geometricPosition (M.geometricParent F covered a.val))
    (last : x ∈ segment ℝ (F.geometricPosition b.val)
      (F.geometricPosition (M.geometricParent F covered b.val)))
    (last_not_end : x ≠ F.geometricPosition (M.geometricParent F covered b.val)) : a = b := by
  apply Subtype.ext
  by_contra different
  have endpoints := M.geometric_parent_intersection_endpoints F covered positive small lower
    a.val b.val different a.property b.property first last
  exact different (F.geometricPosition_injective lower
    ((endpoints.1.resolve_right first_not_end).symm.trans
      (endpoints.2.resolve_right last_not_end)))

/-- The half-open geometric parent edges partition all cuts except the outer terminal tips. -/
theorem exists_unique_geometric_forward_edge {x : Plane} (member : x ∈ M.extendedGeometricCuts F)
    (not_tip : x ∉ Set.range (fun c : F.Component => (F.componentTail c).tip)) :
    ∃! e : {w : F.GeometricVertex //
        w ∉ (M.geometricParents F covered positive small lower).roots},
      x ∈ segment ℝ (F.geometricPosition e.val)
        (F.geometricPosition (M.geometricParent F covered e.val)) ∧
        x ≠ F.geometricPosition (M.geometricParent F covered e.val) := by
  let P := M.geometricParents F covered positive small lower
  have on_edge : x ∈ M.geometricEdgeCarrier F covered positive small lower := by
    have either := (M.extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips F covered
      positive small lower).subset member
    exact either.resolve_right not_tip
  obtain ⟨e, on_segment⟩ := Set.mem_iUnion.mp on_edge
  have exists_edge : ∃ e : {w : F.GeometricVertex // w ∉ P.roots},
      x ∈ segment ℝ (F.geometricPosition e.val)
        (F.geometricPosition (P.parent e.val)) ∧ x ≠ F.geometricPosition (P.parent e.val) := by
    by_cases at_end : x = F.geometricPosition (P.parent e.val)
    · have nonroot : P.parent e.val ∉ P.roots := by
        rintro ⟨c, same⟩
        exact not_tip ⟨c, (congrArg F.geometricPosition same).trans at_end.symm⟩
      refine ⟨⟨P.parent e.val, nonroot⟩, ?_, ?_⟩
      · exact at_end ▸ left_mem_segment ℝ _ _
      · intro same
        have positions : F.geometricPosition (P.parent e.val) =
            F.geometricPosition (P.parent (P.parent e.val)) := at_end.symm.trans same
        have equal := F.geometricPosition_injective lower positions
        have ascending := P.ascending (P.parent e.val) nonroot
        rw [← equal] at ascending
        exact lt_irrefl _ ascending
    · exact ⟨e, on_segment, at_end⟩
  obtain ⟨e, segment, not_end⟩ := exists_edge
  refine ⟨e, ⟨segment, not_end⟩, fun d properties => ?_⟩
  exact M.geometric_halfOpen_parent_unique F covered positive small lower d e
    properties.1 properties.2 segment not_end

end Unfoldings.ConvexCap.SectorForest
