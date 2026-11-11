module

public import Unfoldings.Cap.ExtendedCutParents

/-! The explicit geometric parent forest represents the entire original-and-skirt cut set. -/

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

def geometricEdgeCarrier : Set Plane :=
  ⋃ e : {w : F.GeometricVertex // w ∉ (M.geometricParents F covered positive small lower).roots},
    segment ℝ (F.geometricPosition e.val)
      (F.geometricPosition ((M.geometricParents F covered positive small lower).parent e.val))

theorem geometric_original_nonroot (w : C.Vertex Set.univ) :
    Sum.inl w ∉ (M.geometricParents F covered positive small lower).roots := by
  rintro ⟨c, impossible⟩
  cases impossible

theorem geometric_independent_nonroot (c : F.IndependentComponent) :
    Sum.inr (Sum.inl c) ∉ (M.geometricParents F covered positive small lower).roots := by
  rintro ⟨d, impossible⟩
  cases impossible

/-- Degenerate components consist of their outer tip alone. Every genuine segment is an edge
of the explicit geometric forest, with original rim roots attached exactly once. -/
theorem extendedGeometricCuts_eq_geometricEdgeCarrier_union_tips :
    M.extendedGeometricCuts F = M.geometricEdgeCarrier F covered positive small lower ∪
      Set.range (fun c : F.Component => (F.componentTail c).tip) := by
  classical
  let P := M.geometricParents F covered positive small lower
  apply Set.Subset.antisymm
  · intro x member
    rcases member with original | skirt
    · obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp original
      have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
      left
      refine Set.mem_iUnion.mpr
        ⟨⟨Sum.inl e.val, M.geometric_original_nonroot F covered positive small lower e.val⟩, ?_⟩
      change x ∈ segment ℝ (K.projectedVertex e.val)
        (F.geometricPosition (P.parent (Sum.inl e.val)))
      rw [M.geometricParents_original_parent F covered positive small lower e.val internal]
      exact on_edge
    · obtain ⟨c, on_component⟩ := Set.mem_iUnion.mp skirt
      by_cases genuine : F.componentSeed c ≠ (F.componentTail c).tip
      · by_cases attached : ∃ w : C.Vertex Set.univ,
            C.IsBoundaryVertex Set.univ w ∧ K.projectedVertex w = F.componentSeed c
        · obtain ⟨w, boundary, seed⟩ := attached
          have component : F.rimComponent covered w boundary = c :=
            F.rimComponent_eq_of_member lower covered w boundary c
              (seed.symm ▸ (F.componentTail c).seed_mem)
          left
          refine Set.mem_iUnion.mpr
            ⟨⟨Sum.inl w, M.geometric_original_nonroot F covered positive small lower w⟩, ?_⟩
          change x ∈ segment ℝ (K.projectedVertex w)
            (F.geometricPosition (P.parent (Sum.inl w)))
          rw [M.geometricParents_rim_parent F covered positive small lower w boundary]
          change x ∈ segment ℝ (K.projectedVertex w)
            (F.componentTail (F.rimComponent covered w boundary)).tip
          rw [component, seed]
          exact on_component
        · let d : F.IndependentComponent := ⟨c, genuine, attached⟩
          left
          refine Set.mem_iUnion.mpr
            ⟨⟨Sum.inr (Sum.inl d),
              M.geometric_independent_nonroot F covered positive small lower d⟩, on_component⟩
      · right
        have same : F.componentSeed c = (F.componentTail c).tip := not_ne_iff.mp genuine
        have at_tip : x = (F.componentTail c).tip := by
          change x ∈ segment ℝ (F.componentSeed c) (F.componentTail c).tip at on_component
          rw [same, segment_same] at on_component
          exact Set.mem_singleton_iff.mp on_component
        exact ⟨c, at_tip.symm⟩
  · intro x member
    rcases member with edge | tip
    · obtain ⟨⟨w, nonroot⟩, on_edge⟩ := Set.mem_iUnion.mp edge
      cases w with
      | inl w =>
        by_cases boundary : C.IsBoundaryVertex Set.univ w
        · right
          refine Set.mem_iUnion.mpr ⟨F.rimComponent covered w boundary, ?_⟩
          change x ∈ segment ℝ (K.projectedVertex w)
            (F.geometricPosition (P.parent (Sum.inl w))) at on_edge
          rw [M.geometricParents_rim_parent F covered positive small lower w boundary] at on_edge
          have seed := F.rim_vertex_eq_seed _ w boundary (F.rimComponent_mem covered w boundary)
          rw [seed] at on_edge
          exact on_edge
        · left
          have old_nonroot : w ∉ M.parents.roots := by
            simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
          refine Set.mem_iUnion.mpr ⟨⟨w, old_nonroot⟩, ?_⟩
          change x ∈ segment ℝ (K.projectedVertex w)
            (F.geometricPosition (P.parent (Sum.inl w))) at on_edge
          rw [M.geometricParents_original_parent F covered positive small lower w boundary]
            at on_edge
          exact on_edge
      | inr w =>
        cases w with
        | inl c => exact Or.inr (Set.mem_iUnion.mpr ⟨c.val, on_edge⟩)
        | inr c => exact (nonroot ⟨c, rfl⟩).elim
    · obtain ⟨c, rfl⟩ := tip
      exact Or.inr (Set.mem_iUnion.mpr ⟨c, (F.componentTail c).tip_mem⟩)

end Unfoldings.ConvexCap.SectorForest
