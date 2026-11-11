module

public import Unfoldings.Cap.ExtendedCutLabels
public import Unfoldings.Cap.RimTails

/-! Each complete extended geometric cut component has one acute direction wedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

theorem parent_roots_eq_of_component_label
    (a b : {w : C.Vertex Set.univ // w ∉ M.parents.roots})
    (same : M.cutPieceLabel F covered (Sum.inl a) = M.cutPieceLabel F covered (Sum.inl b)) :
    M.parents.root a.val = M.parents.root b.val := by
  let c := M.cutPieceLabel F covered (Sum.inl a)
  have first : K.projectedVertex (M.parents.root a.val) ∈ (F.componentTail c).carrier :=
    F.rimComponent_mem covered _ (M.rootPath_end_boundary a.val)
  have last : K.projectedVertex (M.parents.root b.val) ∈ (F.componentTail c).carrier := by
    have member := F.rimComponent_mem covered _ (M.rootPath_end_boundary b.val)
    exact (congrArg (fun d => (F.componentTail d).carrier) same.symm).subset member
  exact F.rim_vertices_eq_of_component c _ _ (M.rootPath_end_boundary a.val)
    (M.rootPath_end_boundary b.val) first last

theorem root_sector_label (nonnegative : 0 ≤ t) (small : t < 1)
    (w : C.Vertex Set.univ) :
    K.sourceSectorLabel t origin (M.parents.root w) = K.sourceSectorLabel t origin w := by
  have label := M.iterate_label nonnegative small w (M.parents.distanceToRoot w)
  rw [M.parents.iterate_distanceToRoot_eq_root] at label
  exact label

/-- Attached original trees use their old three-sector wedge. Independent radial components
use their single ray, of width zero. Auxiliary cap vertices need no new empty-gap assumption. -/
theorem exists_cut_component_wedge (positive : 0 < t) (small : t < 1) (c : F.Component) :
    ∃ u v : Plane, u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v < Real.pi / 2 ∧
      ∀ i : M.ExtendedCutPiece F, M.cutPieceLabel F covered i = c →
        InDirectionWedge u v (M.cutPieceLast F i - M.cutPieceFirst F i) := by
  classical
  by_cases attached : ∃ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) = c
  · obtain ⟨e, at_c⟩ := attached
    let i := K.sourceSectorLabel t origin e.val
    have banks := threeSector_banks_inner_pos positive small i
    have first_ne : threeSectorRay t i.castSucc ≠ 0 := by
      intro zero
      rw [zero, inner_zero_left] at banks
      exact lt_irrefl _ banks
    have last_ne : threeSectorRay t i.succ ≠ 0 := by
      intro zero
      rw [zero, inner_zero_right] at banks
      exact lt_irrefl _ banks
    refine ⟨threeSectorRay t i.castSucc, threeSectorRay t i.succ, first_ne, last_ne,
      threeSectorWidth_lt_pi_div_two positive small i, ?_⟩
    intro j same
    cases j with
    | inl f =>
      have roots := M.parent_roots_eq_of_component_label F covered f e (same.trans at_c.symm)
      have label : K.sourceSectorLabel t origin f.val = i :=
        (M.root_sector_label positive.le small f.val).symm.trans
          ((congrArg (K.sourceSectorLabel t origin) roots).trans
            (M.root_sector_label positive.le small e.val))
      have direction := M.direction f.val f.property
      rw [label] at direction
      exact inDirectionWedge_of_closedThreeSector positive.le small i
        (strictThreeSector_subset_closed t i direction)
    | inr d =>
      change d = c at same
      subst d
      have member : K.projectedVertex (M.parents.root e.val) ∈ (F.componentTail c).carrier :=
        (congrArg (fun d => (F.componentTail d).carrier) at_c).subset
          (F.rimComponent_mem covered _ (M.rootPath_end_boundary e.val))
      obtain ⟨a, nonnegative, direction⟩ :=
        (F.componentTail c).direction_eq_nonneg_smul_of_mem member
      change (F.componentTail c).tip - F.componentSeed c =
        a • (K.projectedVertex (M.parents.root e.val) - K.projectedVertex origin) at direction
      have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
      have root_direction := (M.root_radial_direction positive.le small
        ((K.projectedVertex_mem_interior_iff origin).mp F.origin) e.val internal).1
      have wedge := inDirectionWedge_of_closedThreeSector positive.le small i root_direction
      obtain ⟨r, s, rnonnegative, snonnegative, representation⟩ := wedge
      refine ⟨a * r, a * s, mul_nonneg nonnegative rnonnegative,
        mul_nonneg nonnegative snonnegative, ?_⟩
      change (F.componentTail c).tip - F.componentSeed c = _
      rw [direction, representation, smul_add, smul_smul, smul_smul]
  · let u := (F.componentTail c).tip - K.projectedVertex origin
    have genuine : u ≠ 0 := by
      intro zero
      have equal : (F.componentTail c).tip = K.projectedVertex origin := sub_eq_zero.mp zero
      exact F.component_outside c (F.componentTail c).tip_mem (equal.symm ▸ F.origin)
    refine ⟨u, u, genuine, genuine, ?_, ?_⟩
    · rw [InnerProductGeometry.angle_self genuine]
      positivity
    · intro j same
      cases j with
      | inl e => exact (attached ⟨e, same⟩).elim
      | inr d =>
        change d = c at same
        subst d
        obtain ⟨a, nonnegative, direction⟩ :=
          (F.componentTail c).direction_eq_nonneg_smul_of_mem (F.componentTail c).tip_mem
        change (F.componentTail c).tip - F.componentSeed c = a • u at direction
        refine ⟨a, 0, nonnegative, le_rfl, ?_⟩
        change (F.componentTail c).tip - F.componentSeed c = a • u + (0 : ℝ) • u
        simpa only [zero_smul, add_zero] using direction

end Unfoldings.ConvexCap.SectorForest
