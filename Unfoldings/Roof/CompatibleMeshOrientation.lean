module

public import Unfoldings.Roof.CompatibleMeshPaths
public import Unfoldings.Roof.SeamSegments
public import Unfoldings.Geometry.OrientedSubsegments

/-! Every potential-increasing fine seam is an oriented portion of a unique coarse cut edge. -/

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
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher

include no_boundary positive inner_disk beta acute in
theorem cut_segment_height_injective (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    Set.InjOn (B).height (segment ℝ (R.cutFirst level i) (R.cutLast level higher i)) := by
  intro x hx y hy equal
  obtain ⟨s, hs, at_x⟩ := (segment_eq_image_lineMap ℝ _ _).subset hx
  obtain ⟨t, ht, at_y⟩ := (segment_eq_image_lineMap ℝ _ _).subset hy
  have strict : StrictMonoOn (fun t : ℝ => (B).height
      (AffineMap.lineMap (R.cutFirst level i) (R.cutLast level higher i) t)) (Set.Icc 0 1) :=
    K.truncated_segment_strict compact nonempty R no_boundary level higher positive beta acute
      inner_disk ((Fintype.equivFin (C.Vertex Set.univ)).symm i)
  have same : s = t := strict.injOn hs ht (by simpa only [at_x, at_y] using equal)
  exact at_x.symm.trans ((congrArg (AffineMap.lineMap _ _) same).trans at_y)

include no_boundary positive inner_disk beta acute in
theorem oriented_truncated_subsegment {i : Fin (Fintype.card (C.Vertex Set.univ))} {x y : Plane}
    (first : x ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i))
    (last : y ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i))
    (increasing : (B).height x < (B).height y) :
    Nonempty ((Gcut).OrientedSubsegment x y) := by
  obtain ⟨s, hs, at_first⟩ := (segment_eq_image_lineMap ℝ _ _).subset first
  obtain ⟨t, ht, at_last⟩ := (segment_eq_image_lineMap ℝ _ _).subset last
  let v := (Fintype.equivFin (C.Vertex Set.univ)).symm i
  have strict : StrictMonoOn (fun t : ℝ => (B).height
      (AffineMap.lineMap (R.cutFirst level i) (R.cutLast level higher i) t)) (Set.Icc 0 1) :=
    K.truncated_segment_strict compact nonempty R no_boundary level higher positive beta acute
      inner_disk v
  have ordered : s < t := by
    by_contra reversed
    have bound := strict.monotoneOn ht hs (not_lt.mp reversed)
    rw [at_first, at_last] at bound
    exact (not_lt_of_ge bound) increasing
  refine ⟨{
    edge := ⟨.inl v, R.parents.withLeaves_inl_nonroot level _ v⟩
    first := s
    last := t
    first_mem := hs
    last_mem := ht
    increasing := ordered
    at_first := at_first
    at_last := at_last }⟩

/-- A forward cut portion starts strictly inside the truncating section. -/
theorem oriented_truncated_start_strict {x y : Plane}
    (P : (Gcut).OrientedSubsegment x y) :
    (K.clippedExtension slopes compact nonempty).height x < level := by
  rcases P with ⟨⟨edge, nonroot⟩, s, t, hs, ht, increasing, first, _last⟩
  cases edge with
  | inr r => exact (nonroot ⟨r, rfl⟩).elim
  | inl v =>
    change AffineMap.lineMap (R.truncatedPoint level (.inl v))
      (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) s = x at first
    by_cases zero : s = 0
    · rw [zero, AffineMap.lineMap_apply_zero] at first
      exact first ▸ higher v
    · have inside := R.truncated_segment_height_lt level higher v
        (lineMap_mem_openSegment ℝ _ _ ⟨lt_of_le_of_ne hs.1 (Ne.symm zero),
          increasing.trans_le ht.2⟩)
      rw [first] at inside
      exact inside

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside

local instance compatibleMeshOrientationIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute in
theorem compatibleMesh_oriented_seam {s : (T).pairedComplex.Seam}
    {v w : (T).pairedComplex.Vertex Set.univ} (link : (T).pairedComplex.seamGraph.IsLink s v w)
    (selected : ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
      ((T).pairedComplex.left s).edge ⊆ R.truncatedCarrier level higher)
    (increasing : (B).height ((Q).projectedVertex v) < (B).height ((Q).projectedVertex w)) :
    Nonempty ((Gcut).OrientedSubsegment ((Q).projectedVertex v) ((Q).projectedVertex w)) := by
  obtain ⟨i, contained⟩ := K.compatibleMesh_subedge compact nonempty R no_boundary level higher
    M positive inner_disk ((T).pairedComplex.left s) selected
  have segment_eq := (Q).projected_link_segment link
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at segment_eq
  apply K.oriented_truncated_subsegment compact nonempty R no_boundary level higher
    positive inner_disk beta acute
  · exact contained (segment_eq ▸ left_mem_segment ℝ _ _)
  · exact contained (segment_eq ▸ right_mem_segment ℝ _ _)
  · exact increasing

end Unfoldings.ConvexRoof
