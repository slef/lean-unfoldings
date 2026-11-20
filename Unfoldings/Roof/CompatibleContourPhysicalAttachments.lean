module

public import Unfoldings.Roof.CompatibleContourSourceOnlyTailAddressCoverage
public import Unfoldings.Roof.CompatibleContourSourceOnlyGraft
public import Unfoldings.Roof.CompatibleContourPhysicalAgreement
public import Unfoldings.Geometry.StraightGraphLinks
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Roof.OriginalCutLabels

/-! The physical address of a strict bank point is unique on the complete cut forest. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyPhysicalAttachmentsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)

local instance sourceOnlyPhysicalAttachmentsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Height" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
local notation "Conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "Inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) Conforming Inside
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection
local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "VertexAt[" v "]" => ConvexRoof.projectedVertex Q v

/-- The original physical point of a finite or infinite attachment, with the cut restored. -/
def compatibleContourPhysicalAttachmentPoint (b : Attachment) (t : ParamAt b) : Plane :=
  Cap.horizontal (W.partition.restoreCut R.carrier (Base b false t)).val

local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W

/-- The original finite mark is precisely the projected straight fine parent edge. -/
theorem compatibleContourPhysicalAttachmentPoint_finite (e : Edge) (t : unitInterval) :
    Phys (.inl e) t = AffineMap.lineMap VertexAt[e.val]
      VertexAt[(Fcut).parents.parent e.val] t.val := by
  let fold := (T).pairedFolding
  let f (v : (D).Vertex Set.univ) := fold.toSpace Set.univ ((D).vertexPoint Set.univ v)
  have projected (v : (D).Vertex Set.univ) : Cap.horizontal (f v) = VertexAt[v] := by
    have identity : (D).vertexForgetCuts (Set.subset_univ Set.univ) v = v := by
      obtain ⟨c, rfl⟩ := (D).vertexOfCorner_surjective Set.univ v
      rfl
    exact (((T).toTriangulation.roof_projectedVertex_vertexForgetCuts Conforming Inside
      Set.univ v).symm).trans (congrArg ((Q).projectedVertex) identity)
  unfold compatibleContourPhysicalAttachmentPoint
  have h := congrArg Cap.horizontal (K.restore_compatibleContourParentMark_position
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    e.val e.property false t)
  change _ = Cap.horizontal (AffineMap.lineMap (f e.val)
    (f ((Fcut).parents.parent e.val)) t.val) at h
  exact h.trans ((Cap.horizontal.toAffineMap.apply_lineMap _ _ _).trans
    (congrArg₂ (fun a b : Plane => AffineMap.lineMap a b t.val) (projected _) (projected _)))

/-- Every actual tail parameter retains its original forward time on the physical ray. -/
theorem compatibleContourPhysicalAttachmentPoint_tail (e : Terminal) (t : ℝ≥0) :
    Phys (.inr e) t = R.exterior.ray (R.terminalIndex RootAt[e])
      (R.terminalTime level RootAt[e] + (SpeedAt[e]).val * t.val) :=
  (congrArg Cap.horizontal (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W e false t)).trans
    (SpatialEnvelope.horizontal_point M.plane _)

private theorem compatibleContourPhysicalAttachmentPoint_finite_height_le (e : Edge)
    (t : unitInterval) : Height (Phys (.inl e) t) ≤ level := by
  have in_footprint : AffineMap.lineMap VertexAt[e.val]
      VertexAt[(Fcut).parents.parent e.val] t.val ∈ (Q).footprint :=
    (Q).convex_projection.lineMap_mem ((Q).projectedVertex_mem_footprint e.val)
      ((Q).projectedVertex_mem_footprint ((Fcut).parents.parent e.val)) t.property
  rw [(T).toTriangulation.roof_footprint Conforming Inside, M.clip_eq_sublevel, neg_neg]
    at in_footprint
  rw [K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W e t]
  exact in_footprint

/-- Strict parameters on finite banks are strictly below the original cut level. -/
theorem compatibleContourPhysicalAttachmentPoint_finite_lt (e : Edge) (t : unitInterval)
    (strict : 0 < t.val ∧ t.val < 1) : Height (Phys (.inl e) t) < level := by
  have low := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M
    positive inner_disk beta acute e.val e.property
  have high := K.compatibleContourPhysicalAttachmentPoint_finite_height_le compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W e 1
  rw [K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts W] at high
  change Height (AffineMap.lineMap VertexAt[e.val]
    VertexAt[(Fcut).parents.parent e.val] (1 : ℝ)) ≤ level at high
  rw [AffineMap.lineMap_apply_one] at high
  rw [K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W]
  apply (K.clippedExtension slopes compact nonempty).openSegment_height_lt low high
  rw [openSegment_eq_image_lineMap]
  exact ⟨t.val, strict, rfl⟩

/-- A physical point strictly inside a fine edge has just that original address. -/
theorem compatibleContourPhysicalAttachmentPoint_eq_of_finite_interior
    (e : Edge) (t : unitInterval) (strict : 0 < t.val ∧ t.val < 1)
    (b : Attachment) (s : ParamAt b) (equal : Phys b s = Phys (.inl e) t) :
    (⟨b, s⟩ : Σ a : Attachment, ParamAt a) = ⟨.inl e, t⟩ := by
  have open_edge : Phys (.inl e) t ∈
      openSegment ℝ VertexAt[e.val] VertexAt[(Fcut).parents.parent e.val] := by
    rw [K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W, openSegment_eq_image_lineMap]
    exact ⟨t.val, strict, rfl⟩
  have off_vertices (v : (D).Vertex Set.univ) : Phys (.inl e) t ≠ VertexAt[v] := fun h =>
    (Q).seamEmbedding_straight.openSegment_avoids_vertices ((Selection).link e)
      (h ▸ open_edge)
  cases b with
  | inr f =>
    have lower := K.compatibleContourPhysicalAttachmentPoint_finite_lt compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e t strict
    have at_tail := K.compatibleContourPhysicalAttachmentPoint_tail compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W f s
    have upper : level ≤ Height (Phys (.inr f) s) := by
      rw [at_tail]
      have elapsed : R.terminalTime level RootAt[f] ≤
          R.terminalTime level RootAt[f] + (SpeedAt[f]).val * s.val :=
        le_add_of_nonneg_right (mul_nonneg (SpeedAt[f]).property s.property)
      exact (R.terminal_ray_superlevel_iff level higher _ ((R.terminalTime_pos level higher
        _).le.trans elapsed)).mpr elapsed
    exact (not_lt_of_ge (Eq.mp (congrArg (fun p => level ≤ Height p) equal) upper) lower).elim
  | inl f =>
    have first := K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W f s
    have second := K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W e t
    have bounds : 0 < s.val ∧ s.val < 1 := by
      constructor
      · apply lt_of_le_of_ne s.property.1
        intro h
        rw [← h, AffineMap.lineMap_apply_zero] at first
        exact off_vertices f.val (equal.symm.trans first)
      · apply lt_of_le_of_ne s.property.2
        intro h
        rw [h, AffineMap.lineMap_apply_one] at first
        exact off_vertices ((Fcut).parents.parent f.val) (equal.symm.trans first)
    have same : f = e := by
      by_contra different
      have at_edge : Phys (.inl e) t ∈
          openSegment ℝ VertexAt[f.val] VertexAt[(Fcut).parents.parent f.val] := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨s.val, bounds, first.symm.trans equal⟩
      exact Set.disjoint_left.mp ((Q).seamEmbedding_straight.openSegments_disjoint
        (fun eq => different ((Selection).edge_injective eq)) ((Selection).link f)
        ((Selection).link e)) at_edge open_edge
    subst f
    have ends_ne : VertexAt[e.val] ≠ VertexAt[(Fcut).parents.parent e.val] := by
      intro h
      exact ((Fcut).parents.ascending e.val e.property).ne
        (congrArg (Fcut).parents.height ((Q).projectedVertex_injective h))
    have time : s = t := Subtype.ext (AffineMap.lineMap_injective ℝ ends_ne
      (first.symm.trans (equal.trans second)))
    exact congrArg (fun u : unitInterval => (⟨.inl e, u⟩ : Σ a : Attachment, ParamAt a)) time

/-- Every point past a terminal join has just one original physical bank address. -/
theorem compatibleContourPhysicalAttachmentPoint_eq_of_positive_tail
    (e : Terminal) (t : ℝ≥0) (positive_time : 0 < t)
    (a : Attachment) (s : ParamAt a) (equal : Phys a s = Phys (.inr e) t) :
    (⟨a, s⟩ : Σ a : Attachment, ParamAt a) = ⟨.inr e, t⟩ := by
  let rayTime (r : Terminal) (u : ℝ≥0) := R.terminalTime level RootAt[r] + (SpeedAt[r]).val * u.val
  have time_pos (r : Terminal) (u : ℝ≥0) : 0 < rayTime r u :=
    (R.terminalTime_pos level higher _).trans_le
      (le_add_of_nonneg_right (mul_nonneg (SpeedAt[r]).property u.property))
  have time_lt : R.terminalTime level RootAt[e] < rayTime e t :=
    lt_add_of_pos_right _ (mul_pos
      (K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W e) positive_time)
  have ray (r : Terminal) (u : ℝ≥0) :
      Phys (.inr r) u = R.exterior.ray (R.terminalIndex RootAt[r]) (rayTime r u) :=
    K.compatibleContourPhysicalAttachmentPoint_tail compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W r u
  cases a with
  | inl v =>
    have below := K.compatibleContourPhysicalAttachmentPoint_finite_height_le compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W v s
    have bound : Height (R.exterior.ray (R.terminalIndex RootAt[e]) (rayTime e t)) ≤ level :=
      Eq.mp (congrArg (fun q => Height q ≤ level) (equal.trans (ray e t))) below
    exact ((not_le_of_gt time_lt) ((R.terminal_ray_sublevel_iff level higher
      RootAt[e] (time_pos e t).le).mp bound)).elim
  | inr r =>
    have same_ray := (ray r s).symm.trans (equal.trans (ray e t))
    have roots : RootAt[r] = RootAt[e] := by
      by_contra h
      have different : (RootAt[r]).val ≠ (RootAt[e]).val := fun h' => h (Subtype.ext h')
      exact Set.disjoint_left.mp
        (K.compatible_openPieces_pairwise_disjoint compact nonempty R no_boundary different)
        (R.terminal_ray_mem_openPiece RootAt[r] (time_pos r s))
        (same_ray.symm ▸ R.terminal_ray_mem_openPiece RootAt[e] (time_pos e t))
    have same_edge := K.compatibleContourTerminalRoot_injective compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W roots
    subst r
    have h := congrArg Height same_ray
    rw [R.exterior.height_ray _ (time_pos e s).le, R.exterior.height_ray _ (time_pos e t).le] at h
    have times : rayTime e s = rayTime e t :=
      mul_right_cancel₀ (R.exterior.positive (R.terminalIndex RootAt[e])).ne' (add_left_cancel h)
    have sp := K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W e
    have time : s = t := by
      apply NNReal.eq
      change R.terminalTime level RootAt[e] + (SpeedAt[e]).val * s.val =
        R.terminalTime level RootAt[e] + (SpeedAt[e]).val * t.val at times
      exact mul_left_cancel₀ sp.ne' (add_left_cancel times)
    exact congrArg (fun u : ℝ≥0 => (⟨.inr e, u⟩ : Σ a : Attachment, ParamAt a)) time

end Unfoldings.ConvexRoof
