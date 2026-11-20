module

public import Unfoldings.Roof.CompatibleMeshOrientation
public import Unfoldings.Roof.CompatibleMeshForest

/-! Strict potential increase along every point of an actual compatible parent edge. -/

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

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside

local instance compatibleMeshOrderedParentsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

private theorem strictMono_on_forward_subsegment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (value : E → ℝ) (a b x y : E)
    (strict : StrictMonoOn (fun t : ℝ => value (AffineMap.lineMap a b t)) (Set.Icc 0 1))
    (first : x ∈ segment ℝ a b) (last : y ∈ segment ℝ a b) (increasing : value x < value y) :
    StrictMono (fun t : unitInterval => value (AffineMap.lineMap x y t.val)) := by
  obtain ⟨s, hs, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset first
  obtain ⟨r, hr, at_y⟩ := (segment_eq_image_lineMap ℝ a b).subset last
  have forward : s < r := by
    by_contra! reversed
    have back := strict.monotoneOn hr hs reversed
    rw [at_x, at_y] at back
    exact (not_lt_of_ge back) increasing
  intro t u after
  have at_t : AffineMap.lineMap s r t.val ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc _ _).segment_subset hs hr (lineMap_mem_segment ℝ _ _ t.property)
  have at_u : AffineMap.lineMap s r u.val ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc _ _).segment_subset hs hr (lineMap_mem_segment ℝ _ _ u.property)
  have order : AffineMap.lineMap s r t.val < AffineMap.lineMap s r u.val := by
    have spaced := mul_pos (sub_pos.mpr (show t.val < u.val from after)) (sub_pos.mpr forward)
    simp only [AffineMap.lineMap_apply_module', smul_eq_mul]
    nlinarith
  have it := (AffineMap.lineMap a b).apply_lineMap s r t.val
  have iu := (AffineMap.lineMap a b).apply_lineMap s r u.val
  change value (AffineMap.lineMap x y t.val) < value (AffineMap.lineMap x y u.val)
  rw [← at_x, ← at_y, ← it, ← iu]
  exact strict at_t at_u order

/-- Every actual parent edge progresses strictly throughout its projected segment,
with the original affine edge parameter. -/
theorem compatibleMeshParentEdge_strictPotential
    (v : (T).pairedComplex.Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots) :
    StrictMono (fun t : unitInterval => (B).height
      (AffineMap.lineMap ((Q).projectedVertex v)
        ((Q).projectedVertex ((Fcut).parents.parent v)) t.val)) := by
  let e := (⟨v, nonroot⟩ : {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots})
  let s := (Fcut).selection.edge e
  have selected := (Fcut).selected_subset e
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at selected
  obtain ⟨i, contained⟩ := K.compatibleMesh_subedge compact nonempty R no_boundary level higher
    M positive inner_disk ((T).pairedComplex.left s) selected
  have eq := (Q).projected_link_segment ((Fcut).selection.link e)
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at eq
  have first := contained (eq ▸ left_mem_segment ℝ _ _)
  have last := contained (eq ▸ right_mem_segment ℝ _ _)
  have progress := (Fcut).parents.ascending v nonroot
  rw [(Fcut).height_eq] at progress
  exact strictMono_on_forward_subsegment (B).height _ _ _ _
    (K.truncated_segment_strict compact nonempty R no_boundary level higher positive beta acute
      inner_disk ((Fintype.equivFin (C.Vertex Set.univ)).symm i)) first last progress

end Unfoldings.ConvexRoof
