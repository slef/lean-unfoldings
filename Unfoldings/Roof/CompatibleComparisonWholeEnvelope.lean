module

public import Unfoldings.Roof.CompatibleComparisonPhysicalCompletion
public import Unfoldings.Roof.CompatibleMeshWholeEnvelope

/-! Larger comparison meshes and physical completions preserve the original whole roof. -/

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

local instance comparisonWholeEnvelopeIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "HigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "VAt[" L "," h "]" => R.levelWindowModel M L HigherAt[L,h]
local notation "ProperAt[" L "," h "]" => R.levelWindow_proper M L HigherAt[L,h]
local notation "FullAt[" L "," h "]" => R.levelWindow_full M L HigherAt[L,h]
local notation "DomainAt[" L "]" => SpatialEnvelope.levelEquation_domain M.plane (-L)
local notation "Heights" => Set.eqOn_refl (SpatialEnvelope.height M.plane) _
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_cut_disjoint_interior compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S L h
local notation "ConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RemovedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.removed_edge_mem_cut
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RetainedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.retained_openSeamImage_disjoint
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S L h)

open Classical in
local instance comparisonWholeEnvelopeNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonWholeEnvelopeWholeFintype : Fintype W.Index := W.finiteIndex

local notation "NewRoofAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
  ConformingAt[S,L,h]
  (K.compatible_section_interior compact nonempty R L HigherAt[L,h] M)
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

/-- Choose a common larger window after capturing every whole support cell. The
same choice works for every intermediate parent frontier. -/
theorem exists_compatibleMeshProcessedComparison_support_level (lower : ℝ) :
    ∃ later : ℝ, level < later ∧ lower < later ∧
      ∀ c, (interior (W.partition.footprint c) ∩
        interior (SpatialEnvelope.clip M.plane (-later))).Nonempty := by
  obtain ⟨later, large, captured⟩ :=
    SpatialEnvelope.exists_level_capturing_support_cells W.partition (max level lower)
  exact ⟨later, (le_max_left _ _).trans_lt large, (le_max_right _ _).trans_lt large,
    captured later le_rfl⟩

/-- Capturing all original support cells keeps the entire unbounded roof, even
outside the constructed comparison mesh and independently of the current cuts. -/
theorem compatibleMeshProcessedComparisonRoofHeight_eq_whole
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (captured : ∀ c, (interior (W.partition.footprint c) ∩
      interior (SpatialEnvelope.clip M.plane (-later))).Nonempty) (p : Plane) :
    (NewRoofAt[S,later,ordered]).roofHeight p = SpatialEnvelope.height M.plane p :=
  (NewAt[S,later,ordered]).toTriangulation.roofHeight_eq_whole_height
    ConformingAt[S,later,ordered]
    (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M) captured p

/-- Original face constraints and arbitrary additional comparison lines construct
physical completions that preserve the original whole graph on the requested region. -/
theorem exists_compatibleMeshProcessedComparison_completion_preserving_whole_roof
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (captured : ∀ c, (interior (W.partition.footprint c) ∩
      interior (SpatialEnvelope.clip M.plane (-later))).Nonempty)
    {φ : ℝ} (tilt_positive : 0 < φ) (tilt_small : φ < Real.pi / 2)
    {region : Set Plane} (region_compact : IsCompact region)
    {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0) :
    ∃ E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
        ((NewRoofAt[S,later,ordered]).combinedCompletionEquations extra),
      ∀ p ∈ region,
        SpatialEnvelope.height
            ((NewRoofAt[S,later,ordered]).completionPlanes E.tentHeight (Real.sin φ / 2)) p =
          SpatialEnvelope.height M.plane p := by
  obtain ⟨E, preserved⟩ := (NewRoofAt[S,later,ordered]).exists_combined_completion extra
    tilt_positive tilt_small region_compact proper
  exact ⟨E, fun p member => (preserved p member).trans
    (K.compatibleMeshProcessedComparisonRoofHeight_eq_whole compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered captured p)⟩

end Unfoldings.ConvexRoof
