module

public import Unfoldings.Cap.GeometricSectorBoundaryLeaves

/-! Beyond its starting leaf, an actual tail can meet a sector bank only on its radial skirt. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (w : M.GeometricSectorLeaf F covered positive small lower i)

theorem tail_bank_contact_radial {h : ℝ} {x : Plane}
    (at_point : (fiveSectorFrame t positive small i).place
      (x - K.projectedVertex origin) = w.tailGraph.graph.point h)
    (start : w.point.re + w.point.im < h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w.val)
    (bank : x - K.projectedVertex origin ∉ strictFiveSector t i) :
    x ∈ (F.componentTail (M.geometricComponent F covered w.val)).carrier := by
  let B := fiveSectorFrame t positive small i
  let Q := M.geometricParents F covered positive small lower
  let P := M.geometricRootPath F covered positive small lower B.place w.val
  let A := centeredPlaneFrame (K.projectedVertex origin) B.place
  obtain ⟨j, s, on_path⟩ := P.heightGraph_point_on_chain w.tailGraph.graph w.tailGraph.pieces
    (fun j => add_pos (w.tailGraph.positive_steps j).1 (w.tailGraph.positive_steps j).2)
    h start.le finish
  let z := (M.geometricParent F covered)^[j.val] w.val
  have nonroot : z ∉ Q.roots := Q.iterate_lt_distanceToRoot_not_mem w.val j.isLt
  have component : M.geometricComponent F covered z = M.geometricComponent F covered w.val :=
    M.geometricComponent_iterate F covered w.val j.val
  have first : A (F.geometricPosition z) = P.vertex j.castSucc := centeredPlaneFrame_apply _ _ _
  have last : A (F.geometricPosition (M.geometricParent F covered z)) = P.vertex j.succ := by
    rw [centeredPlaneFrame_apply]
    change B.place (F.geometricPosition (M.geometricParent F covered z) -
      K.projectedVertex origin) = B.place
        (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] w.val) -
          K.projectedVertex origin)
    rw [Function.iterate_succ_apply']
  have on_segment : A x ∈ segment ℝ (A (F.geometricPosition z))
      (A (F.geometricPosition (M.geometricParent F covered z))) := by
    rw [first, last]
    rw [show A x = B.place (x - K.projectedVertex origin) from
      centeredPlaneFrame_apply _ _ _, at_point, on_path]
    exact lineMap_mem_segment ℝ _ _ s.property
  have image : A '' segment ℝ (F.geometricPosition z)
      (F.geometricPosition (M.geometricParent F covered z)) =
        segment ℝ (A (F.geometricPosition z))
          (A (F.geometricPosition (M.geometricParent F covered z))) :=
    image_segment ℝ A.toAffineMap _ _
  obtain ⟨y, member, equal⟩ := image.symm.subset on_segment
  have physical : x ∈ segment ℝ (F.geometricPosition z)
      (F.geometricPosition (M.geometricParent F covered z)) := A.injective equal ▸ member
  obtain ⟨piece, piece_first, piece_last, label⟩ :=
    M.geometric_parent_piece F covered positive small lower z nonroot
  rw [← piece_first, ← piece_last] at physical
  cases piece with
  | inr c =>
    have same : c = M.geometricComponent F covered w.val := label.trans component
    rw [← same]
    exact physical
  | inl e =>
    have sector : Sum.inl (K.sourceSectorLabel t origin e.val) = i := by
      rw [← M.geometricComponentSector_original_parent F covered positive small lower e]
      have edge_component : M.geometricComponent F covered (Sum.inl e.val) =
          M.geometricComponent F covered w.val := label.trans component
      rw [edge_component]
      exact w.property.2.2
    have closed := closedFiveSector_coordinates positive small i (w.component_positions z component)
    rw [← piece_first] at closed
    have strict : K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val ∈
        strictFiveSector t i := sector ▸ M.direction e.val e.property
    obtain ⟨r, bounds, expression⟩ := (segment_eq_image_lineMap ℝ
      (M.cutPieceFirst F (Sum.inl e)) (M.cutPieceLast F (Sum.inl e))).subset physical
    by_cases zero : r = 0
    · have at_child : x = F.geometricPosition z := by
        rw [zero, AffineMap.lineMap_apply_zero, piece_first] at expression
        exact expression.symm
      have child_bank : F.geometricPosition z - K.projectedVertex origin ∉
          strictFiveSector t (M.geometricComponentSector F covered positive small lower
            (M.geometricComponent F covered z)).sector := by
        rw [component, w.property.2.2, ← at_child]
        exact bank
      have childless := M.geometric_sector_bank_childless F covered positive small lower z
        nonroot child_bank
      have same : w.val = z := (Q.ancestor_childless_iff nonroot childless w.val).mp ⟨j.val, rfl⟩
      have position : x = F.geometricPosition w.val := at_child.trans
        (congrArg F.geometricPosition same.symm)
      have height := w.tailGraph.graph.point_height h
      rw [← at_point, position] at height
      exact (start.ne height).elim
    · have rpositive : 0 < r := lt_of_le_of_ne bounds.1 (Ne.symm zero)
      apply (bank ?_).elim
      have vector : x - K.projectedVertex origin =
          (K.projectedVertex e.val - K.projectedVertex origin) +
            r • (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
        rw [← expression, AffineMap.lineMap_apply_module']
        change r • (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) +
          K.projectedVertex e.val - K.projectedVertex origin = _
        abel
      rw [vector]
      change 0 < fiveSectorCoordinates t i _ 0 ∧ 0 < fiveSectorCoordinates t i _ 1
      rw [map_add, map_smul]
      exact ⟨add_pos_of_nonneg_of_pos closed.1 (mul_pos rpositive strict.1),
        add_pos_of_nonneg_of_pos closed.2 (mul_pos rpositive strict.2)⟩

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
