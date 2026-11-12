module

public import Unfoldings.Cap.CompletedBankPhysicalSides
public import Unfoldings.Cap.CompletedSubtreeDirections
public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Cap.ProjectedSeamFaces
public import Unfoldings.Geometry.HeightGraphSegments
public import Unfoldings.Geometry.WedgeFrameSides

/-! Named entrance and exit faces have the required signs relative to their actual cut graphs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector)
  (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val ∈ closedFiveSector t i)

include direction in
theorem parentCutGraph_steps :
    let frame := (fiveSectorFrame t positive small i).place
    0 < (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).re -
      (frame (K.projectedVertex e.val - source)).re ∧
    0 < (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).im -
      (frame (K.projectedVertex e.val - source)).im := by
  let B := fiveSectorFrame t positive small i
  have quadrant := B.quadrant_self direction (N.completed_parent_direction_ne_zero e.val e.property)
  have movement :
      B.place (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source) -
        B.place (K.projectedVertex e.val - source) =
      B.place (K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
        K.projectedVertex e.val) := by
    rw [← B.place.map_sub]
    congr 1
    abel
  rw [← movement, Complex.sub_re, Complex.sub_im] at quadrant
  exact quadrant

def parentCutGraph : MonotoneHeightGraph :=
  let frame := (fiveSectorFrame t positive small i).place
  let steps := N.parentCutGraph_steps positive small i e direction
  MonotoneHeightGraph.through (frame (K.projectedVertex e.val - source))
    (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source))
    (sub_pos.mp steps.1).le (sub_pos.mp steps.2).le (by linarith [steps.1, steps.2])

theorem parentCutGraph_framed_mem_segment {p : Plane}
    (member : p ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    let frame := (fiveSectorFrame t positive small i).place
    frame (p - source) ∈ segment ℝ (frame (K.projectedVertex e.val - source))
      (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)) := by
  let A := centeredPlaneFrame source (fiveSectorFrame t positive small i).place
  have image : A '' segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) =
      segment ℝ (A (K.projectedVertex e.val))
        (A (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :=
    image_segment ℝ A.toAffineMap _ _
  have mapped := image.subset ⟨p, member, rfl⟩
  simpa only [A, centeredPlaneFrame_apply] using mapped

theorem parentCutGraph_coordinate_of_mem_segment {p : Plane}
    (member : p ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))) :
    let frame := (fiveSectorFrame t positive small i).place
    (N.parentCutGraph positive small i e direction).coordinate
      ((frame (p - source)).re + (frame (p - source)).im) = (frame (p - source)).re := by
  let steps := N.parentCutGraph_steps positive small i e direction
  exact MonotoneHeightGraph.through_coordinate_of_mem_segment _ _
    (sub_pos.mp steps.1).le (sub_pos.mp steps.2).le (by linarith [steps.1, steps.2])
    (N.parentCutGraph_framed_mem_segment positive small i e member)

include direction in
theorem parentCutGraph_strict_height {p : Plane}
    (member : p ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)))
    (first : p ≠ K.projectedVertex e.val)
    (last : p ≠ K.projectedVertex (N.spanningCompletion.parents.parent e.val)) :
    let frame := (fiveSectorFrame t positive small i).place
    (frame (p - source)).re + (frame (p - source)).im ∈ Set.Ioo
      ((frame (K.projectedVertex e.val - source)).re +
        (frame (K.projectedVertex e.val - source)).im)
      ((frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).re +
        (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).im) := by
  let frame := (fiveSectorFrame t positive small i).place
  have steps := N.parentCutGraph_steps positive small i e direction
  apply linear_segment_strict_bounds complexDiagonalHeight
    (a := frame (K.projectedVertex e.val - source))
    (b := frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source))
    (x := frame (p - source)) (by
    change (frame (K.projectedVertex e.val - source)).re +
      (frame (K.projectedVertex e.val - source)).im <
      (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).re +
      (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).im
    linarith [steps.1, steps.2])
    (N.parentCutGraph_framed_mem_segment positive small i e member)
  · intro equal
    exact first (sub_left_injective (frame.injective equal))
  · intro equal
    exact last (sub_left_injective (frame.injective equal))

theorem parentCutGraph_avoids_strict_strip (on_cut : K.projectedVertex e.val ∈ cuts)
    (S : MonotoneStrip) (cutoff : ℝ)
    (avoids : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
      source + (fiveSectorFrame t positive small i).place.symm z ∉ cuts)
    {h : ℝ}
    (inside : h ∈ Set.Icc
      (((fiveSectorFrame t positive small i).place (K.projectedVertex e.val - source)).re +
        ((fiveSectorFrame t positive small i).place (K.projectedVertex e.val - source)).im)
      (((fiveSectorFrame t positive small i).place
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).re +
        ((fiveSectorFrame t positive small i).place
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).im))
    (slab : h ∈ Set.Icc 0 cutoff) :
    (N.parentCutGraph positive small i e direction).point h ∉ S.strictCarrier := by
  let steps := N.parentCutGraph_steps positive small i e direction
  exact framed_cut_segment_avoids_strict_strip source (fiveSectorFrame t positive small i).place
    cuts _ _ (N.completed_parent_segment_subset_cuts e on_cut) S cutoff avoids
    (sub_pos.mp steps.1).le (sub_pos.mp steps.2).le (by linarith [steps.1, steps.2]) inside slab

theorem parentCutGraph_entrance_side (D : FacewiseDevelopment C N.completedRetain)
    {z : ℂ} (member : source + (fiveSectorFrame t positive small i).place.symm z ∈
      (K.projectedTriangle (N.parentBankOpening D e).entranceFace).carrier) :
    (N.parentCutGraph positive small i e direction).coordinate (z.re + z.im) ≤ z.re := by
  let B := fiveSectorFrame t positive small i
  let steps := N.parentCutGraph_steps positive small i e direction
  apply (MonotoneHeightGraph.through_side_nonpos_iff _ _
    (sub_pos.mp steps.1).le (sub_pos.mp steps.2).le (by linarith [steps.1, steps.2]) z).mpr
  exact (B.centered_orient_nonpos_iff (fiveSector_banks_orient_pos positive small i)
    source (K.projectedVertex e.val)
    (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) z).mpr
      (N.parent_entrance_face_side D e member)

theorem parentCutGraph_exit_side (D : FacewiseDevelopment C N.completedRetain)
    {z : ℂ} (member : source + (fiveSectorFrame t positive small i).place.symm z ∈
      (K.projectedTriangle (N.parentBankOpening D e).exitFace).carrier) :
    z.re ≤ (N.parentCutGraph positive small i e direction).coordinate (z.re + z.im) := by
  let B := fiveSectorFrame t positive small i
  let steps := N.parentCutGraph_steps positive small i e direction
  apply (MonotoneHeightGraph.through_side_nonneg_iff _ _
    (sub_pos.mp steps.1).le (sub_pos.mp steps.2).le (by linarith [steps.1, steps.2]) z).mpr
  exact (B.centered_orient_nonneg_iff (fiveSector_banks_orient_pos positive small i)
    source (K.projectedVertex e.val)
    (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) z).mpr
      (N.parent_exit_face_side D e member)

theorem parent_bank_faces_of_regular (D : FacewiseDevelopment C N.completedRetain)
    {p : Plane} (member : p ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val)))
    (regular : ∀ f j, p ≠ (K.projectedTriangle f).vertex j) :
    ∀ f, p ∈ (K.projectedTriangle f).carrier →
      f = (N.parentBankOpening D e).entranceFace ∨ f = (N.parentBankOpening D e).exitFace := by
  let O := N.parentBankOpening D e
  have on_edge := (N.parent_segment_eq_original_seam e).subset member
  intro f in_face
  have faces := K.projected_face_eq_seamSide_of_regular
    (N.spanningCompletion.selection.edge e) on_edge in_face regular
  rw [O.entranceFace_eq, O.exitFace_eq]
  cases side : O.side
  · simpa only [side, Bool.not_false, TriangleComplex.seamSide, ite_true, ite_false] using faces
  · simpa only [side, Bool.not_true, TriangleComplex.seamSide, ite_true, ite_false] using faces.symm

end Unfoldings.ConvexCap.RadialCutForest
