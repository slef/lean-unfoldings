module

public import Unfoldings.Roof.GeometricComponentNetwork

/-! Every nonterminal geometric cut vertex has an actual containing piece with its own label. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_vertex_mem_labeled_cut_piece (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots) :
    ∃ j : M.ExtendedCutPiece F,
      M.cutPieceLabel F covered j = M.geometricComponent F covered w ∧
      F.geometricPosition w ∈ segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j) := by
  cases w with
  | inl w =>
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · let c := F.rimComponent covered w boundary
      refine ⟨Sum.inr c, (M.geometricComponent_rim F covered w boundary).symm, ?_⟩
      exact F.rimComponent_mem covered w boundary
    · have old_nonroot : w ∉ M.parents.roots := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
      exact ⟨Sum.inl ⟨w, old_nonroot⟩, rfl, left_mem_segment ℝ _ _⟩
  | inr w =>
    cases w with
    | inl c => exact ⟨Sum.inr c.val, rfl, left_mem_segment ℝ _ _⟩
    | inr c => exact (nonroot ⟨c, rfl⟩).elim

end Unfoldings.ConvexRoof.SectorForest
