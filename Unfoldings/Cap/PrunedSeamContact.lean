module

public import Unfoldings.Cap.CurvaturePrunedForest
public import Unfoldings.Cap.ProjectedPointCopies

/-! Pruning removes every coincident pair of regular banks at the same physical cap point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- Every remaining cut separates its two actual incident-face copies before the child endpoint. -/
theorem curved_cut_projected_placements_ne (s : C.Seam) (cut : s ∉ M.curvedRetain)
    {p : Plane}
    (member : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : p ∉ Set.range K.projectedVertex)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    D.projectedPlacement K (C.left s).face p ≠
      D.projectedPlacement K (C.right s).face p := by
  obtain ⟨e, named, _curved⟩ := M.curved_cut_subtree_positive cut
  subst s
  have on_segment : p ∈ segment ℝ (K.projectedVertex (M.parents.parent e.val))
      (K.projectedVertex e.val) := by
    rw [segment_symm, M.parent_segment_eq_original_seam e]
    exact member
  obtain ⟨parameter, bounds, at_point⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_segment
  have before : parameter < 1 := lt_of_le_of_ne bounds.2 (by
    intro equal
    have vertex := at_point
    rw [equal, AffineMap.lineMap_apply_one] at vertex
    exact regular ⟨e.val, vertex⟩)
  have separated := B.curved_parent_bank_interiors_ne e cut before before budget
  rw [M.parentEntrancePoint_eq_projectedPlacement, M.parentExitPoint_eq_projectedPlacement,
    at_point] at separated
  let O := M.parentBankOpening D e
  intro same
  apply separated
  cases side : O.side
  · simpa only [O, (M.parentBankOpening D e).entranceFace_eq,
      (M.parentBankOpening D e).exitFace_eq, side, TriangleComplex.seamSide,
      Bool.not_false] using same
  · simpa only [O, (M.parentBankOpening D e).entranceFace_eq,
      (M.parentBankOpening D e).exitFace_eq, side, TriangleComplex.seamSide,
      Bool.not_true] using same.symm

include B in
/-- At a common physical nonvertex point, coincident face copies are intrinsically equal
once all zero-curvature descendant subtrees have been restored. -/
theorem curved_pointCopy_eq_of_same_physical_point (f g : Face) {p : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier)
    (last : p ∈ (K.projectedTriangle g).carrier)
    (regular : p ∉ Set.range K.projectedVertex)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (same : D.projectedPlacement K f p = D.projectedPlacement K g p) :
    K.pointCopy M.curvedRetain f p first = K.pointCopy M.curvedRetain g p last := by
  by_cases equal : f = g
  · subst g
    rfl
  have nonvertex : ¬ (K.projectedTriangle f).IsVertex p := by
    rintro ⟨i, vertex⟩
    exact regular ⟨C.vertexOfCorner Set.univ (f, i), vertex⟩
  obtain ⟨e, h, shared, on_edge⟩ :=
    (K.projectedTriangles_conforming f g equal p ⟨first, last⟩).resolve_left
      (fun vertices => nonvertex vertices.1)
  obtain ⟨s, ⟨left, right⟩ | ⟨left, right⟩⟩ :=
    K.exists_seam_of_projected_shared_edge (a := ⟨f, e⟩) (b := ⟨g, h⟩) equal shared
  · have at_left : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
      simpa only [left] using on_edge
    by_cases kept : s ∈ M.curvedRetain
    · simpa only [left, right] using K.pointCopy_eq_across_seam M.curvedRetain s kept at_left
    · have separated := curved_cut_projected_placements_ne B s kept at_left regular budget
      exact (separated (by simpa only [left, right] using same)).elim
  · have at_left : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
      simpa only [left] using shared ▸ on_edge
    by_cases kept : s ∈ M.curvedRetain
    · simpa only [left, right] using
        (K.pointCopy_eq_across_seam M.curvedRetain s kept at_left).symm
    · have separated := curved_cut_projected_placements_ne B s kept at_left regular budget
      exact (separated (by simpa only [left, right] using same.symm)).elim

end Unfoldings.ConvexCap.SectorForest
