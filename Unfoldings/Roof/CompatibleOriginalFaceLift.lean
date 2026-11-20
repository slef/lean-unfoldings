module

public import Unfoldings.Geometry.SpatialEnvelopeFaceLift
public import Unfoldings.Roof.CompatibleCutClosed
public import Unfoldings.Roof.CompatibleCutEmbedding
public import Unfoldings.Roof.CompatibleWholeCutModel
public import Unfoldings.Roof.SeamSegments
public import Unfoldings.Complex.SelectedCuts
public import Unfoldings.Roof.OriginalCuts

/-! Recover literal original face copies from the complete compatible cut roof. -/

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
/-- Away from original vertices, only selected original seams can cut a selected face. -/
theorem compatibleCarrier_mem_iff_original_cut
    (f : Face) (selected : K.normalSlope f ∈ slopes) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier)
    (nonvertex : ∀ v, p ≠ K.projectedVertex v) :
    p ∈ R.carrier ↔
      p ∈ K.projectedCutSet (C.selectedRetain R.original.selection) := by
  classical
  constructor
  · rintro (finite | ray)
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp finite
      by_cases root : v.val ∈ R.original.parents.roots
      · have open_edge : p ∈ openSegment ℝ (K.projectedVertex v.val)
            (K.projectedVertex (R.parents.parent v.val)) := by
          rw [segment_eq_image_lineMap] at hv
          obtain ⟨t, ht, eq⟩ := hv
          rw [openSegment_eq_image_lineMap]
          refine ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ?_), lt_of_le_of_ne ht.2 ?_⟩, eq⟩
          · intro zero
            exact nonvertex v.val (eq.symm.trans ((congrArg _ zero).trans
              (AffineMap.lineMap_apply_zero ..)))
          · intro one
            exact nonvertex (R.parents.parent v.val) (eq.symm.trans ((congrArg _ one).trans
              (AffineMap.lineMap_apply_one ..)))
        have selected_p := K.mem_selectedCarrier.mpr ⟨f, selected, member⟩
        exact (Set.disjoint_left.mp (K.exterior_piece_disjoint_selected compact nonempty R
          no_boundary ⟨v.val, root⟩) (R.exterior_segment_subset_openPiece root v.property open_edge)
          selected_p).elim
      · let e := R.original.selection.edge ⟨v.val, root⟩
        have edge_segment := K.projected_link_segment (R.original.selection.link ⟨v.val, root⟩)
        have removed : e ∉ C.selectedRetain R.original.selection := fun h => h ⟨⟨v.val, root⟩, rfl⟩
        have parent := R.original_parent root
        change p ∈ segment ℝ (K.projectedVertex v.val)
          (K.projectedVertex (R.parents.parent v.val)) at hv
        rw [parent, edge_segment] at hv
        exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨removed, hv⟩⟩
    · obtain ⟨v, t, t_nonneg, equal⟩ := Set.mem_iUnion.mp ray
      by_cases t_zero : t = 0
      · subst t
        have start : R.exterior.ray (R.terminalIndex v) 0 = K.projectedVertex v.val := by
          simp only [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points]
          rfl
        exact (nonvertex v.val (equal.trans start)).elim
      · exact (K.compatible_exterior_ray_avoids_selected compact nonempty R no_boundary
          (R.terminalIndex v) (lt_of_le_of_ne t_nonneg (Ne.symm t_zero)) f selected
          (equal ▸ member)).elim
  · intro h
    obtain ⟨e, on_e⟩ := Set.mem_iUnion.mp h
    obtain ⟨removed, on_e⟩ := Set.mem_iUnion.mp on_e
    obtain ⟨v, rfl⟩ := Classical.not_not.mp removed
    have nonroot : v.val ∉ R.parents.roots := fun root => v.property root.1
    have same := K.projected_link_segment (R.original.selection.link v)
    exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v.val, nonroot⟩,
      (R.original_parent v.property).symm ▸ (same.symm ▸ on_e)⟩)

/-- A projected original vertex is never in the interior of a projected original face. -/
private theorem projectedVertex_not_mem_face_interior (v : C.Vertex Set.univ) (f : Face) :
    K.projectedVertex v ∉ interior (K.projectedTriangle f).carrier := by
  obtain ⟨⟨g, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  rw [K.projectedVertex_ofCorner]
  intro inside
  have same := K.projected_face_unique_of_interior inside ((K.projectedTriangle g).vertex_mem i)
  subst g
  exact (K.projectedTriangle f).not_mem_interior_of_mem_edge i
    (left_mem_segment ℝ _ _) inside

include no_boundary in
/-- No compatible forest cut enters the interior of a selected original face. -/
theorem compatibleCarrier_avoids_original_face_interior (f : Face)
    (selected : K.normalSlope f ∈ slopes) {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier) : p ∉ R.carrier := by
  intro at_cut
  have nonvertex (v : C.Vertex Set.univ) : p ≠ K.projectedVertex v :=
    fun h => K.projectedVertex_not_mem_face_interior v f (h ▸ inside)
  have original := (K.compatibleCarrier_mem_iff_original_cut compact nonempty R no_boundary
    f selected (interior_subset inside) nonvertex).mp at_cut
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp original
  obtain ⟨_, on_e⟩ := Set.mem_iUnion.mp he
  exact K.projected_seam_not_mem_face_interior e f inside on_e

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)

local instance originalFaceLiftIndexFintype (W : R.WholeCutModel M) : Fintype W.Index :=
  W.finiteIndex

/-- The original selected face lies in the restored spatial envelope at its exact placement. -/
theorem original_face_subset_wholeSurface (f : Face) (selected : K.normalSlope f ∈ slopes) :
    K.folding.place f '' (C.triangle f).carrier ⊆ SpatialEnvelope.wholeSurface M.plane := by
  rintro _ ⟨x, hx, rfl⟩
  let p := K.projectFace f x
  have in_face : p ∈ (K.projectedTriangle f).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨x, hx, rfl⟩
  refine ⟨p, ?_⟩
  ext i
  fin_cases i
  · rfl
  · rfl
  · change SpatialEnvelope.height M.plane p = K.folding.place f x 2
    rw [M.height_eq, K.clippedExtension_preserves_original_face compact nonempty f selected in_face,
      neg_neg]
    exact K.roofHeight_face f ⟨x, hx⟩

include no_boundary in
/-- Each selected original triangle has a rigid lift to the whole cut roof. -/
theorem exists_compatible_original_face_lift (W : R.WholeCutModel M) (f : Face)
    (selected : K.normalSlope f ∈ slopes) :
    ∃ lift : C.Cell f → W.Cut, Isometry lift ∧
      ∀ x, (W.partition.restoreCut R.carrier (lift x)).val = K.folding.place f x.val := by
  apply W.partition.exists_cut_face_lift R.carrier R.isClosed_carrier
    (C.triangle f).convex_carrier (C.triangle f).interior_nonempty (K.folding.place f)
    (K.original_face_subset_wholeSurface compact nonempty M f selected)
  intro x hx
  apply K.compatibleCarrier_avoids_original_face_interior compact nonempty R no_boundary f selected
  have hc : (K.projectFaceHomeomorph f) '' (C.triangle f).carrier = (K.projectedTriangle f).carrier :=
    ((C.triangle f).affineImage_carrier (K.projectFace f) (K.projectFace_injective f)).symm
  rw [← hc, ← Homeomorph.image_interior]
  exact ⟨x, hx, rfl⟩

end Unfoldings.ConvexRoof
