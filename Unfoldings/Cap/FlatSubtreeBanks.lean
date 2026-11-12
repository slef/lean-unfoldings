module

public import Unfoldings.Cap.OriginalBankFaceValues
public import Unfoldings.Cap.ParentSegments
public import Unfoldings.Development.RestoreSeams

/-! Original parent seams bounding zero-curvature subtrees are actual removable flat slits. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

theorem subtreeCurvature_mono {v e : C.Vertex Set.univ} (reaches : M.parents.Ancestor v e) :
    M.subtreeCurvature v ≤ M.subtreeCurvature e := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w member
    exact (M.parents.mem_descendants w e).mpr
      (((M.parents.mem_descendants w v).mp member).trans M.parents reaches)
  · exact fun w _ _ => K.interiorCurvature_nonneg w

theorem subtreeCurvature_descendant_zero {v e : C.Vertex Set.univ}
    (reaches : M.parents.Ancestor v e) (flat : M.subtreeCurvature e = 0) :
    M.subtreeCurvature v = 0 :=
  le_antisymm ((M.subtreeCurvature_mono reaches).trans_eq flat) (M.subtreeCurvature_nonneg v)

theorem parent_vectors_eq_of_flat (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (flat : M.subtreeCurvature e.val = 0) :
    M.parentExitVector D e = M.parentEntryVector D e := by
  have rotation := (M.parentBankOpening D e).rotation
  rw [flat, polarRay_zero, one_mul] at rotation
  exact (D.boundaryCycleFrame M.projectionContour.cycle).injective rotation

theorem parent_position_gap_zero_of_flat (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (flat : M.subtreeCurvature e.val = 0) :
    M.parentPositionGap D e = 0 := by
  classical
  rw [M.parent_position_gap_eq_descendant_sum D e]
  apply Finset.sum_eq_zero
  intro v _
  split_ifs with reaches
  · rw [M.parent_vectors_eq_of_flat D v (M.subtreeCurvature_descendant_zero reaches flat), sub_self]
  · rfl

theorem parent_points_eq_of_flat (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (flat : M.subtreeCurvature e.val = 0)
    (s : ℝ) : M.parentExitPoint D e s = M.parentEntrancePoint D e s := by
  have positions := M.parent_position_gap_zero_of_flat D e flat
  have same := sub_eq_zero.mp positions
  change _ - _ = _ - _
  rw [M.parent_vectors_eq_of_flat D e flat]
  exact congrArg (fun p => p - s • M.parentEntryVector D e) same

theorem parent_seam_coherent_of_flat (D : FacewiseDevelopment C M.retain)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (flat : M.subtreeCurvature e.val = 0) :
    M.selection.edge e ∈ D.coherentSeams := by
  let O := M.parentBankOpening D e
  intro x
  let p := K.projectFace (C.left (M.selection.edge e)).face x.val
  have on_edge : p ∈ (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
      (C.left (M.selection.edge e)).edge := by
    rw [projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩
  have on_segment : p ∈ segment ℝ (K.projectedVertex (M.parents.parent e.val))
      (K.projectedVertex e.val) := by
    rw [segment_symm, M.parent_segment_eq_original_seam e]
    exact on_edge
  obtain ⟨s, _within, point⟩ := (segment_eq_image_lineMap ℝ _ _).le on_segment
  have same := M.parent_points_eq_of_flat D e flat s
  rw [M.parentEntrancePoint_eq_projectedPlacement, M.parentExitPoint_eq_projectedPlacement,
    point] at same
  have placements : D.projectedPlacement K (C.left (M.selection.edge e)).face p =
      D.projectedPlacement K (C.right (M.selection.edge e)).face p := by
    cases side : O.side
    · simpa only [O, (M.parentBankOpening D e).entranceFace_eq,
        (M.parentBankOpening D e).exitFace_eq, side, TriangleComplex.seamSide,
        Bool.not_false] using same.symm
    · simpa only [O, (M.parentBankOpening D e).entranceFace_eq,
        (M.parentBankOpening D e).exitFace_eq, side, TriangleComplex.seamSide,
        Bool.not_true] using same
  change D.place (C.left (M.selection.edge e)).face x.val =
    D.place (C.right (M.selection.edge e)).face (C.identify (M.selection.edge e) x).val
  change D.projectedPlacement K (C.left (M.selection.edge e)).face
      (K.projectFace (C.left (M.selection.edge e)).face x.val) =
    D.projectedPlacement K (C.right (M.selection.edge e)).face
      (K.projectFace (C.left (M.selection.edge e)).face x.val) at placements
  rw [D.projectedPlacement_apply] at placements
  rw [K.projectedTriangle_joined (M.selection.edge e) x, D.projectedPlacement_apply] at placements
  exact placements

end Unfoldings.ConvexCap.SectorForest
