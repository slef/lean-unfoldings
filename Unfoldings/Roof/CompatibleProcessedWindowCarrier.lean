module

public import Unfoldings.Roof.CompatibleProcessedCarrier
public import Unfoldings.Roof.ProjectedRemovedSegments
public import Unfoldings.Roof.TerminalBands

/-! Exact finite segments for original intermediate cuts inside larger comparison windows. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance processedWindowCarrierIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

/-- Truncate the same intermediate whole cut at a new comparison level. Its finite old
processed seams stay fixed; only the fixed original outer tails are clipped at the new level. -/
def compatibleMeshProcessedWindowCarrier (S : (Fcut).parents.ParentFrontier) (later : ℝ) :
    Set Plane :=
  (Q).removedProjectedSeamCarrier RetainAt[S] ∪
    ⋃ r : {v // v ∈ R.parents.roots},
      segment ℝ (R.terminalPoint level r) (R.terminalPoint later r)

/-- The new finite cut has exactly the old removed edges and the original terminal segments. -/
theorem compatibleMeshProcessedWindowCarrier_eq_union_edges
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) :
    K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S later =
      (⋃ s : {s : (T).pairedComplex.Seam // s ∉ RetainAt[S]},
        ((Q).projectedTriangle ((T).pairedComplex.left s.val).face).edge
          ((T).pairedComplex.left s.val).edge) ∪
      ⋃ r : {v // v ∈ R.parents.roots},
        segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
  rw [compatibleMeshProcessedWindowCarrier, (Q).removedProjectedSeamCarrier_eq_union_edges]

/-- Every finite processed original seam remains below the original truncation level. -/
theorem compatibleMeshProcessed_removed_sublevel (S : (Fcut).parents.ParentFrontier) :
    (Q).removedProjectedSeamCarrier RetainAt[S] ⊆
      {p | (K.clippedExtension slopes compact nonempty).height p ≤ level} := by
  have footprint := (Q).removedProjectedSeamCarrier_subset_footprint RetainAt[S]
  rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel, neg_neg]
    at footprint
  exact footprint

/-- The finite comparison cut is exactly the original intermediate cut restricted to the
new closed level window. Processing is unchanged when the comparison window grows. -/
theorem compatibleMeshProcessedCarrier_inter_sublevel (S : (Fcut).parents.ParentFrontier)
    {later : ℝ} (ordered : level ≤ later) :
    (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S) ∩
        {p | (K.clippedExtension slopes compact nonempty).height p ≤ later} =
      K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S later := by
  have removed_below : (Q).removedProjectedSeamCarrier RetainAt[S] ⊆
      {p | (K.clippedExtension slopes compact nonempty).height p ≤ later} := by
    intro p member
    exact (K.compatibleMeshProcessed_removed_sublevel compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S member).trans ordered
  have outer : (R.carrier ∩ {p | level ≤
      (K.clippedExtension slopes compact nonempty).height p}) ∩
        {p | (K.clippedExtension slopes compact nonempty).height p ≤ later} =
      ⋃ r : {v // v ∈ R.parents.roots},
        segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
    rw [Set.inter_assoc]
    exact R.carrier_inter_closed_band level higher ordered
  change (_ ∪ _) ∩ _ = _ ∪ _
  rw [Set.union_inter_distrib_right, outer, Set.inter_eq_left.mpr removed_below, Set.union_comm]

/-- Every original cut copy in the larger closed comparison window sees the same cuts. -/
theorem compatibleMeshProcessedWindowCarrier_agree (S : (Fcut).parents.ParentFrontier)
    {later : ℝ} (ordered : level ≤ later) {p : Plane}
    (member : p ∈ SpatialEnvelope.clip M.plane (-later)) :
    p ∈ K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S ↔
      p ∈ K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level higher M
        positive inner_disk beta acute S later := by
  rw [M.clip_eq_sublevel, neg_neg] at member
  rw [← K.compatibleMeshProcessedCarrier_inter_sublevel compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S ordered]
  exact (and_iff_left member).symm

/-- The enlarged finite comparison cut is compact, with every old endpoint retained. -/
theorem isCompact_compatibleMeshProcessedWindowCarrier (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) :
    IsCompact (K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S later) :=
by
  apply (((Q).folding.isCompact_removedSeamCarrier RetainAt[S]).image
    Cap.horizontalCLM.continuous).union
  apply isCompact_iUnion
  intro r
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

end Unfoldings.ConvexRoof
