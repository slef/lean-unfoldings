module

public import Unfoldings.Roof.CompatibleOriginalFaceLift
public import Unfoldings.Geometry.EdgeExt

/-! Literal lifts of adjacent original faces agree across each retained seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)

include no_boundary in
/-- The open part of a retained original seam incident to a selected face avoids the full cut. -/
theorem compatibleCarrier_avoids_open_retained_seam
    (s : C.Seam) (kept : s ∈ C.selectedRetain R.original.selection)
    (selected : K.normalSlope (C.left s).face ∈ slopes)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (nonvertex : ¬ (C.triangle (C.left s).face).IsVertex x) :
    K.projectFace (C.left s).face x.val ∉ R.carrier := by
  let p := K.projectFace (C.left s).face x.val
  let a := C.seamVertex s false
  let b := C.seamVertex s true
  have link : C.seamGraph.IsLink s a b := Or.inl ⟨rfl, rfl⟩
  have open_edge : p ∈ openSegment ℝ (K.projectedVertex a) (K.projectedVertex b) := by
    have first : x.val ≠ (C.triangle (C.left s).face).vertex (C.left s).edge :=
      fun h => nonvertex ⟨_, h.symm⟩
    have last : x.val ≠ (C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge) :=
      fun h => nonvertex ⟨_, h.symm⟩
    have original := mem_openSegment_of_ne_left_right first.symm last.symm x.property
    change K.projectFace (C.left s).face x.val ∈ openSegment ℝ
      ((K.projectedTriangle (C.left s).face).vertex (C.left s).edge)
      ((K.projectedTriangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
    exact (image_openSegment ℝ (K.projectFace (C.left s).face) _ _).subset ⟨x.val, original, rfl⟩
  have nonorig (v : C.Vertex Set.univ) : p ≠ K.projectedVertex v := fun h =>
    K.seamEmbedding_straight.openSegment_avoids_vertices link (h ▸ open_edge)
  have p_member : p ∈ (K.projectedTriangle (C.left s).face).carrier :=
    (K.projectedTriangle (C.left s).face).edge_subset _
      ((K.projected_link_segment link).subset ((openSegment_subset_segment ℝ _ _) open_edge))
  intro cut
  have original := (K.compatibleCarrier_mem_iff_original_cut compact nonempty R no_boundary
    _ selected p_member nonorig).mp cut
  obtain ⟨e, on_e⟩ := Set.mem_iUnion.mp original
  obtain ⟨removed, on_e⟩ := Set.mem_iUnion.mp on_e
  have different : s ≠ e := fun h => removed (h ▸ kept)
  let c := C.seamVertex e false
  let d := C.seamVertex e true
  have link_e : C.seamGraph.IsLink e c d := Or.inl ⟨rfl, rfl⟩
  have on_segment := (K.projected_link_segment link_e).symm.subset on_e
  have open_e := mem_openSegment_of_ne_left_right (Ne.symm (nonorig c))
    (Ne.symm (nonorig d)) on_segment
  exact Set.disjoint_left.mp (K.seamEmbedding_straight.openSegments_disjoint different link link_e)
    open_edge open_e

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (W : R.WholeCutModel M)

local instance originalSeamLiftIndexFintype : Fintype W.Index := W.finiteIndex

include no_boundary in
/-- The closed copies of a retained original seam agree, by continuity from its open edge. -/
theorem compatible_original_face_lifts_join
    (s : C.Seam) (kept : s ∈ C.selectedRetain R.original.selection)
    (selected : K.normalSlope (C.left s).face ∈ slopes)
    (l : C.Cell (C.left s).face → W.Cut) (r : C.Cell (C.right s).face → W.Cut)
    (lc : Continuous l) (rc : Continuous r)
    (hl : ∀ x, (W.partition.restoreCut R.carrier (l x)).val = K.folding.place (C.left s).face x.val)
    (hr : ∀ x, (W.partition.restoreCut R.carrier (r x)).val = K.folding.place (C.right s).face x.val)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    l ((C.triangle (C.left s).face).edgeMap (C.left s).edge x) =
      r ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s x)) := by
  let left := (C.triangle (C.left s).face).edgeMap (C.left s).edge
  let right := (C.triangle (C.right s).face).edgeMap (C.right s).edge
  have left_cont : Continuous left := (show Isometry left from fun _ _ => rfl).continuous
  have right_cont : Continuous right := (show Isometry right from fun _ _ => rfl).continuous
  apply congrFun ((C.triangle (C.left s).face).edge_eq_of_nonvertex (C.left s).edge
    (l ∘ left) (r ∘ right ∘ C.identify s) (lc.comp left_cont)
    (rc.comp (right_cont.comp (C.identify s).continuous)) ?_) x
  intro y regular
  apply W.partition.restoreCut_injective_at R.carrier
  · apply PolygonalPoint.ext
    exact (hl (left y)).trans ((K.folding.joined s y).trans
      (hr (right (C.identify s y))).symm)
  · change Cap.horizontal (W.partition.restoreCut R.carrier (l (left y))).val ∉ R.carrier
    rw [hl]
    exact K.compatibleCarrier_avoids_open_retained_seam compact nonempty R no_boundary
      s kept selected y regular

end Unfoldings.ConvexRoof
