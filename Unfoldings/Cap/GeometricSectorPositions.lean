module

public import Unfoldings.Cap.GeometricCutLabels
public import Unfoldings.Geometry.DirectionWedgeOperations

/-! Choose a sector containing both the positions and the directions of an actual cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {S : Set E} {q p x y u v : E} (T : RadialClipTail S q p)

/-- All positions on one radial component have the same positive ray from the source. -/
theorem position_inDirectionWedge_of_mem (first : x ∈ T.carrier)
    (direction : InDirectionWedge u v (x - q)) (last : y ∈ T.carrier) :
    InDirectionWedge u v (y - q) := by
  obtain ⟨a, positive, at_tip⟩ := T.exists_tip_scale_of_mem first
  have vector : T.tip - q = a • (x - q) := by rw [← at_tip, add_sub_cancel_left]
  obtain ⟨r, bounds, at_y⟩ := T.carrier_eq_image.subset last
  rw [← at_y, add_sub_cancel_left, vector, smul_smul]
  exact direction.nonneg_smul (mul_nonneg (T.start_pos.le.trans bounds.1) positive.le)

end RadialClipTail

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

theorem geometric_component_positions_of_parent (positive : 0 < t) (small : t < 1)
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) (c : F.Component)
    (at_c : M.cutPieceLabel F covered (Sum.inl e) = c) :
    ∀ w : F.GeometricVertex, M.geometricComponent F covered w = c →
      F.geometricPosition w - K.projectedVertex origin ∈
        closedFiveSector t (Sum.inl (K.sourceSectorLabel t origin e.val)) := by
  let i := K.sourceSectorLabel t origin e.val
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  have root_member : K.projectedVertex (M.parents.root e.val) ∈
      (F.componentTail c).carrier :=
    (congrArg (fun d => (F.componentTail d).carrier) at_c).subset
      (F.rimComponent_mem covered _ (M.rootPath_end_boundary e.val))
  have root_position : K.projectedVertex (M.parents.root e.val) - K.projectedVertex origin ∈
      closedFiveSector t (Sum.inl i) :=
    inDirectionWedge_of_closedThreeSector positive.le small i
      (M.root_radial_direction positive.le small
        ((K.projectedVertex_mem_interior_iff origin).mp F.origin) e.val internal).1
  have radial_positions : ∀ x ∈ (F.componentTail c).carrier,
      x - K.projectedVertex origin ∈ closedFiveSector t (Sum.inl i) :=
    fun _ member => (F.componentTail c).position_inDirectionWedge_of_mem
      root_member root_position member
  intro w component
  cases w with
  | inl w =>
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · have label := (M.geometricComponent_rim F covered w boundary).symm.trans component
      exact radial_positions _ ((congrArg (fun d => (F.componentTail d).carrier) label).subset
        (F.rimComponent_mem covered w boundary))
    · have nonroot : w ∉ M.parents.roots := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
      let f : {w : C.Vertex Set.univ // w ∉ M.parents.roots} := ⟨w, nonroot⟩
      have same : M.cutPieceLabel F covered (Sum.inl f) =
          M.cutPieceLabel F covered (Sum.inl e) := component.trans at_c.symm
      have roots := M.parent_roots_eq_of_component_label F covered f e same
      have label : K.sourceSectorLabel t origin w = i :=
        (M.root_sector_label positive.le small w).symm.trans
          ((congrArg (K.sourceSectorLabel t origin) roots).trans
            (M.root_sector_label positive.le small e.val))
      have backward : (K.projectedVertex w - K.projectedVertex origin) 0 ≤ 0 :=
        sub_nonpos.mpr (M.maximal w boundary)
      have position := mem_closedThreeSector_label_of_backward positive.le small backward
      change K.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t (Sum.inl i)
      change K.projectedVertex w - K.projectedVertex origin ∈
        closedThreeSector t (K.sourceSectorLabel t origin w) at position
      rw [label] at position
      exact inDirectionWedge_of_closedThreeSector positive.le small i position
  | inr w =>
    cases w with
    | inl d =>
      change d.val = c at component
      change F.componentSeed d.val - K.projectedVertex origin ∈ _
      rw [component]
      exact radial_positions _ (F.componentTail c).seed_mem
    | inr d =>
      change d = c at component
      subst d
      exact radial_positions _ (F.componentTail c).tip_mem

/-- The same fixed sector contains every source-centered node and every whole-edge direction.
This includes rim-only components and degenerate isolated tips. -/
theorem exists_geometric_component_sector_positions (positive : 0 < t) (small : t < 1)
    (lower : Z < 0) (c : F.Component) :
    ∃ i : FiveSector,
      (∀ w : F.GeometricVertex, M.geometricComponent F covered w = c →
        F.geometricPosition w - K.projectedVertex origin ∈ closedFiveSector t i) ∧
      ∀ w : F.GeometricVertex,
        w ∉ (M.geometricParents F covered positive small lower).roots →
        M.geometricComponent F covered w = c →
          F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
            closedFiveSector t i := by
  classical
  by_cases attached : ∃ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) = c
  · obtain ⟨e, at_c⟩ := attached
    refine ⟨Sum.inl (K.sourceSectorLabel t origin e.val),
      M.geometric_component_positions_of_parent F covered positive small e c at_c, ?_⟩
    intro w nonroot component
    obtain ⟨piece, first, last, label⟩ := M.geometric_parent_piece F covered positive small lower
      w nonroot
    have direction := M.cut_component_directions_of_parent F covered positive small e c at_c
      piece (label.trans component)
    rwa [first, last] at direction
  · obtain ⟨i, tip_inside⟩ := exists_mem_closedFiveSector positive small
      ((F.componentTail c).tip - K.projectedVertex origin)
    have radial_positions : ∀ x ∈ (F.componentTail c).carrier,
        x - K.projectedVertex origin ∈ closedFiveSector t i :=
      fun _ member => (F.componentTail c).position_inDirectionWedge_of_mem
        (F.componentTail c).tip_mem tip_inside member
    refine ⟨i, ?_, ?_⟩
    · intro w component
      cases w with
      | inl w =>
        by_cases boundary : C.IsBoundaryVertex Set.univ w
        · have label := (M.geometricComponent_rim F covered w boundary).symm.trans component
          exact radial_positions _
            ((congrArg (fun d => (F.componentTail d).carrier) label).subset
              (F.rimComponent_mem covered w boundary))
        · have nonroot : w ∉ M.parents.roots := by
            simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
          exact (attached ⟨⟨w, nonroot⟩, component⟩).elim
      | inr w =>
        cases w with
        | inl d =>
          change d.val = c at component
          change F.componentSeed d.val - K.projectedVertex origin ∈ _
          rw [component]
          exact radial_positions _ (F.componentTail c).seed_mem
        | inr d =>
          change d = c at component
          subst d
          exact radial_positions _ (F.componentTail c).tip_mem
    · intro w nonroot component
      obtain ⟨piece, first, last, label⟩ := M.geometric_parent_piece F covered positive small lower
        w nonroot
      cases piece with
      | inl e => exact (attached ⟨e, label.trans component⟩).elim
      | inr d =>
        have same : d = c := label.trans component
        subst d
        obtain ⟨a, nonnegative, direction⟩ :=
          (F.componentTail c).direction_eq_nonneg_smul_of_mem (F.componentTail c).tip_mem
        rw [← last, ← first]
        change (F.componentTail c).tip - F.componentSeed c ∈ closedFiveSector t i
        change (F.componentTail c).tip - F.componentSeed c = _ at direction
        rw [direction]
        exact tip_inside.nonneg_smul nonnegative

end ConvexCap.SectorForest
end Unfoldings
