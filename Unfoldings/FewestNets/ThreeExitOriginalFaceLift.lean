module

public import Unfoldings.FewestNets.ThreeExitWholeCut
public import Unfoldings.Geometry.SpatialEnvelopeFaceLift
public import Unfoldings.Metric.PlanarRayCutBanks
public import Unfoldings.Roof.OriginalCuts
public import Unfoldings.Roof.SeamSegments

/-! Every original triangle lifts isometrically to its side of the complete cut roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "A" => R.stems.choice.parents
local notation "haveComponent" => Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)
local notation "G₀" => K.componentClippedExtension haveComponent compact nonempty
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

theorem wholeCutPiece_root_eq_rayCut (r : {v // v ∈ (A).roots}) :
    R.wholeCutPiece r.val = MetricGluing.rayCut (p r.val) (R.exits.ray (R.exitRoot r) 1) := by
  classical
  rw [wholeCutPiece, dif_pos r.property, MetricGluing.rayCut]
  ext x
  constructor
  · rintro ⟨t, h, rfl⟩
    exact ⟨⟨t, h⟩, (R.exit_ray_lineMap r t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, t.property, (R.exit_ray_lineMap r t).symm⟩

theorem isClosed_wholeCutPiece (x : V) : IsClosed (R.wholeCutPiece x) := by
  classical
  by_cases root : x ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨x, root⟩
    change IsClosed (R.wholeCutPiece r.val)
    rw [R.wholeCutPiece_root_eq_rayCut r]
    exact MetricGluing.isClosed_rayCut _ _
  · rw [wholeCutPiece, dif_neg root]
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed

theorem isClosed_wholeCarrier : IsClosed R.wholeCarrier :=
  isClosed_iUnion_of_finite R.isClosed_wholeCutPiece

/-- Each complete cut lies on an original seam or outside all selected face interiors. -/
theorem wholeCarrier_avoids_original_face_interior (f : Face) (hf : f ∈ U) {x : Plane}
    (inside : x ∈ interior (K.projectedTriangle f).carrier) : x ∉ R.wholeCarrier := by
  classical
  intro member
  obtain ⟨v, on_cut⟩ := Set.mem_iUnion.mp member
  have contained : (K.projectedTriangle f).carrier ⊆ S := fun x hx => Set.mem_iUnion.mpr
    ⟨⟨f, hf⟩, hx⟩
  by_cases root : v ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨v, root⟩
    rw [wholeCutPiece, dif_pos root] at on_cut
    obtain ⟨t, ht, rfl⟩ := on_cut
    rcases eq_or_lt_of_le ht with ht | ht
    · subst t
      have h := interior_mono contained inside
      rw [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.point_eq] at h
      exact (R.root_frontier r).2 h
    · exact R.outside _ t ht (contained (interior_subset inside))
  · rw [wholeCutPiece, dif_neg root] at on_cut
    let q : {u // u ∉ (A).roots} := ⟨v, root⟩
    have support := K.projected_link_segment (R.stems.toThreeExitComponentChoices.edge_link q)
    rw [support] at on_cut
    exact K.projected_seam_not_mem_face_interior _ f inside on_cut

/-- A regular point of a retained seam has a unique whole-cut copy. -/
theorem wholeCarrier_avoids_open_retained_seam (s : C.Seam)
    (kept : s ∉ Set.range R.stems.toThreeExitComponentChoices.edge)
    (selected : (C.left s).face ∈ U)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (nonvertex : ¬ (C.triangle (C.left s).face).IsVertex x) :
    K.projectFace (C.left s).face x.val ∉ R.wholeCarrier := by
  let point := K.projectFace (C.left s).face x.val
  let a := C.seamVertex s false
  let b := C.seamVertex s true
  have link : C.seamGraph.IsLink s a b := Or.inl ⟨rfl, rfl⟩
  have open_edge : point ∈ openSegment ℝ (K.projectedVertex a) (K.projectedVertex b) := by
    have first : x.val ≠ (C.triangle (C.left s).face).vertex (C.left s).edge :=
      fun h => nonvertex ⟨_, h.symm⟩
    have last : x.val ≠ (C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge) :=
      fun h => nonvertex ⟨_, h.symm⟩
    have original := mem_openSegment_of_ne_left_right first.symm last.symm x.property
    change K.projectFace (C.left s).face x.val ∈ openSegment ℝ
      ((K.projectedTriangle (C.left s).face).vertex (C.left s).edge)
      ((K.projectedTriangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
    exact (image_openSegment ℝ (K.projectFace (C.left s).face) _ _).subset ⟨x.val, original, rfl⟩
  have nonorig (v : C.Vertex Set.univ) : point ≠ K.projectedVertex v := fun same =>
    K.seamEmbedding_straight.openSegment_avoids_vertices link (same ▸ open_edge)
  have inside : point ∈ S := by
    refine Set.mem_iUnion.mpr ⟨⟨(C.left s).face, selected⟩,
      (K.projectedTriangle (C.left s).face).edge_subset (C.left s).edge ?_⟩
    exact (K.projected_link_segment link).subset ((openSegment_subset_segment ℝ _ _) open_edge)
  intro cut
  classical
  obtain ⟨v, contains⟩ := Set.mem_iUnion.mp cut
  by_cases root : v ∈ (A).roots
  · rw [wholeCutPiece, dite_eq_left root] at contains
    obtain ⟨t, ht, eq⟩ := contains
    rcases eq_or_lt_of_le ht with zero | pos
    · subst t
      rw [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.point_eq] at eq
      exact nonorig _ eq
    · apply R.outside _ _ pos
      rw [← eq]
      exact inside
  · rw [wholeCutPiece, dite_eq_right root] at contains
    let e : {v // v ∉ (A).roots} := ⟨v, root⟩
    have other := R.stems.toThreeExitComponentChoices.edge_link e
    have different : s ≠ R.stems.toThreeExitComponentChoices.edge e :=
      fun same => kept ⟨e, same.symm⟩
    have open_other := mem_openSegment_of_ne_left_right
      (Ne.symm (nonorig v.val)) (Ne.symm (nonorig ((A).parent v).val)) contains
    exact Set.disjoint_left.mp (K.seamEmbedding_straight.openSegments_disjoint different link other)
      open_edge open_other

variable (M : SlopeEnvelope.FiniteSlopeModel
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty))

theorem original_face_subset_wholeSurface (f : Face) (selected : f ∈ U)
    (seed_selected : K.normalSlope seed ∈ slopes) :
    K.folding.place f '' (C.triangle f).carrier ⊆ SpatialEnvelope.wholeSurface (I := M.Face) M.plane := by
  rintro _ ⟨x, hx, rfl⟩
  let projected := K.projectFace f x
  have in_face : projected ∈ (K.projectedTriangle f).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨x, hx, rfl⟩
  refine ⟨projected, ?_⟩
  ext i
  fin_cases i
  · rfl
  · rfl
  · change SpatialEnvelope.height M.plane projected = K.folding.place f x 2
    rw [M.height_eq, K.componentClippedExtension_preserves_face haveComponent compact nonempty
      ⟨f, selected⟩ (K.selectionComponent_selected seed_selected selected) in_face, neg_neg]
    exact K.roofHeight_face f ⟨x, hx⟩

/-- The cut metric contains each original selected triangle on its actual side. -/
theorem exists_original_face_lift (W : R.WholeCutModel M) (f : Face) (selected : f ∈ U)
    (seed_selected : K.normalSlope seed ∈ slopes) :
    ∃ lift : C.Cell f → W.Cut, Isometry lift ∧
      ∀ x, (W.partition.restoreCut R.wholeCarrier (lift x)).val = K.folding.place f x.val := by
  apply W.partition.exists_cut_face_lift R.wholeCarrier R.isClosed_wholeCarrier
    (C.triangle f).convex_carrier (C.triangle f).interior_nonempty (K.folding.place f)
    (original_face_subset_wholeSurface M f selected seed_selected)
  intro x hx
  apply R.wholeCarrier_avoids_original_face_interior f selected
  have image : (K.projectFaceHomeomorph f) '' (C.triangle f).carrier =
      (K.projectedTriangle f).carrier :=
    ((C.triangle f).affineImage_carrier (K.projectFace f) (K.projectFace_injective f)).symm
  rw [← image, ← Homeomorph.image_interior]
  exact ⟨x, hx, rfl⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
