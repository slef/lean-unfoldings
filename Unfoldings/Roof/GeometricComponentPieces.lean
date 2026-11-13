module

public import Unfoldings.Roof.GeometricSectorData

/-! Whole physical cut pieces retain their geometric component's chosen sector data. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small c)

/-- Every original cut or radial continuation with this component label has the
chosen direction sector, and all its points have the same source-position sector. -/
theorem cut_piece_geometry (j : M.ExtendedCutPiece F) (same : M.cutPieceLabel F covered j = c) :
    (M.cutPieceLast F j - M.cutPieceFirst F j ∈ closedFiveSector t data.sector) ∧
      ∀ p ∈ segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j),
        p - origin ∈ closedFiveSector t data.sector := by
  cases j with
  | inl e =>
    have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
      simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
    have parent : M.geometricParent F covered (Sum.inl e.val) =
        Sum.inl (M.parents.parent e.val) :=
      M.geometricParents_original_parent F covered positive small e.val internal
    have direction := data.directions (Sum.inl e.val)
      (M.geometric_original_nonroot F covered positive small e.val) same
    have first := data.positions (Sum.inl e.val) same
    have last := data.positions (M.geometricParent F covered (Sum.inl e.val))
      ((M.geometricComponent_parent F covered (Sum.inl e.val)).trans same)
    rw [parent] at direction last
    change K.projectedVertex e.val - origin ∈ _ at first
    change K.projectedVertex (M.parents.parent e.val) - origin ∈ _ at last
    refine ⟨direction, fun p member => ?_⟩
    let A := AffineEquiv.constVAdd ℝ Plane (-origin)
    have image : A '' segment ℝ (M.cutPieceFirst F (Sum.inl e))
        (M.cutPieceLast F (Sum.inl e)) =
          segment ℝ (A (M.cutPieceFirst F (Sum.inl e)))
            (A (M.cutPieceLast F (Sum.inl e))) := image_segment ℝ A.toAffineMap _ _
    have first' : A (M.cutPieceFirst F (Sum.inl e)) ∈ closedFiveSector t data.sector := by
      change -origin + K.projectedVertex e.val ∈ _
      simpa only [sub_eq_add_neg, add_comm] using first
    have last' : A (M.cutPieceLast F (Sum.inl e)) ∈ closedFiveSector t data.sector := by
      change -origin + K.projectedVertex (M.parents.parent e.val) ∈ _
      simpa only [sub_eq_add_neg, add_comm] using last
    have inside := (convex_inDirectionWedge (fiveSectorFirst t data.sector)
      (fiveSectorLast t data.sector)).segment_subset first' last' (image.subset ⟨p, member, rfl⟩)
    change InDirectionWedge _ _ (-origin + p) at inside
    change InDirectionWedge (fiveSectorFirst t data.sector) (fiveSectorLast t data.sector)
      (p - origin)
    simpa only [sub_eq_add_neg, add_comm] using inside
  | inr d =>
    change d = c at same
    subst d
    have tip := data.positions (Sum.inr (Sum.inr c)) rfl
    change (F.componentTail c).tip - origin ∈
      closedFiveSector t data.sector at tip
    obtain ⟨r, nonnegative, direction⟩ :=
      (F.componentTail c).direction_eq_nonneg_smul_of_mem (F.componentTail c).tip_mem
    constructor
    · change (F.componentTail c).tip - F.componentSeed c ∈ _
      change (F.componentTail c).tip - F.componentSeed c = _ at direction
      rw [direction]
      exact tip.nonneg_smul nonnegative
    · intro p member
      exact (F.componentTail c).position_inDirectionWedge_of_mem
        (F.componentTail c).tip_mem tip member

end Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector
