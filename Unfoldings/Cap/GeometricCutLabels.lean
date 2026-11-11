module

public import Unfoldings.Cap.ExtendedCutCarrier
public import Unfoldings.Cap.ExtendedComponentSectors

/-! Component labels and fixed sectors on the complete geometric cut parent forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SkirtTailFamily

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} {q : Plane} (F : K.SkirtTailFamily Z q)
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

theorem rimComponent_congr {a b : C.Vertex Set.univ}
    (first : C.IsBoundaryVertex Set.univ a) (last : C.IsBoundaryVertex Set.univ b)
    (same : a = b) : F.rimComponent covered a first = F.rimComponent covered b last := by
  subst b
  rfl

end Unfoldings.ConvexCap.SkirtTailFamily

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

def geometricComponent : F.GeometricVertex → F.Component :=
  Sum.elim (fun w => F.rimComponent covered (M.parents.root w) (M.rootPath_end_boundary w))
    (Sum.elim (fun c => c.val) (fun c => c))

theorem geometricComponent_rim (w : C.Vertex Set.univ)
    (boundary : C.IsBoundaryVertex Set.univ w) :
    M.geometricComponent F covered (Sum.inl w) = F.rimComponent covered w boundary := by
  have root : w ∈ M.parents.roots := by simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
  exact F.rimComponent_congr covered (M.rootPath_end_boundary w) boundary
    (M.parents.root_of_root root)

theorem geometricComponent_parent (w : F.GeometricVertex) :
    M.geometricComponent F covered (M.geometricParent F covered w) =
      M.geometricComponent F covered w := by
  cases w with
  | inl w =>
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · simp only [geometricParent, dite_eq_left boundary]
      exact (M.geometricComponent_rim F covered w boundary).symm
    · simp only [geometricParent, dite_eq_right boundary]
      exact F.rimComponent_congr covered (M.rootPath_end_boundary (M.parents.parent w))
        (M.rootPath_end_boundary w)
        (M.parents.root_eq_of_ancestor (M.parents.ancestor_parent w)).symm
  | inr w => cases w <;> rfl

theorem geometricComponent_iterate (w : F.GeometricVertex) (n : ℕ) :
    M.geometricComponent F covered ((M.geometricParent F covered)^[n] w) =
      M.geometricComponent F covered w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', M.geometricComponent_parent, ih]

/-- Each nonconstant geometric parent edge is exactly one original or radial cut piece. -/
theorem geometric_parent_piece (positive : 0 < t) (small : t < 1) (lower : Z < 0)
    (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots) :
    ∃ i : M.ExtendedCutPiece F,
      M.cutPieceFirst F i = F.geometricPosition w ∧
      M.cutPieceLast F i = F.geometricPosition (M.geometricParent F covered w) ∧
      M.cutPieceLabel F covered i = M.geometricComponent F covered w := by
  cases w with
  | inl w =>
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · let c := F.rimComponent covered w boundary
      refine ⟨Sum.inr c, ?_, ?_, ?_⟩
      · exact (F.rim_vertex_eq_seed c w boundary (F.rimComponent_mem covered w boundary)).symm
      · simp only [geometricParent, dite_eq_left boundary]
        rfl
      · exact (M.geometricComponent_rim F covered w boundary).symm
    · have original_nonroot : w ∉ M.parents.roots := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
      refine ⟨Sum.inl ⟨w, original_nonroot⟩, rfl, ?_, rfl⟩
      simp only [geometricParent, dite_eq_right boundary]
      rfl
  | inr w =>
    cases w with
    | inl c => exact ⟨Sum.inr c.val, rfl, rfl, rfl⟩
    | inr c => exact (nonroot ⟨c, rfl⟩).elim

/-- One of the five fixed sectors contains every genuine edge of a whole geometric component. -/
theorem exists_geometric_component_sector (positive : 0 < t) (small : t < 1) (lower : Z < 0)
    (c : F.Component) :
    ∃ i : FiveSector, ∀ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered w = c →
        F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
          closedFiveSector t i := by
  obtain ⟨i, directions⟩ := M.exists_cut_component_sector F covered positive small c
  refine ⟨i, fun w nonroot component => ?_⟩
  obtain ⟨piece, first, last, label⟩ := M.geometric_parent_piece F covered positive small lower w
    nonroot
  have inside := directions piece (label.trans component)
  rwa [first, last] at inside

end Unfoldings.ConvexCap.SectorForest
