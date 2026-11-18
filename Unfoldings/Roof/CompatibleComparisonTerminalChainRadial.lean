module

public import Unfoldings.Roof.CompatibleComparisonTerminalChainTurns
public import Unfoldings.Geometry.RadialMarginSubdivision
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Geometry.RadialChain

/-! Actual spatial endpoint angles and one-sided turn bounds of comparison terminal chains. -/

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

local instance comparisonTerminalChainRadialIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalChainRadialNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChainRadialWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {r : {v // v ∈ R.parents.roots}} {side : Bool}
  (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered r side)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}

open Classical in
/-- The initial original ray margin survives every actual terminal comparison bank without loss. -/
theorem CompatibleComparisonTerminalChainModel.radial_margin
    (source : Plane) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : γ * (‖R.terminalPoint level r - source‖ *
        ‖R.exterior.direction (R.exterior.slope (R.terminalIndex r))‖) ≤
      inner ℝ (R.terminalPoint level r - source)
        (R.exterior.direction (R.exterior.slope (R.terminalIndex r))))
    (i : Fin (D.length + 1)) :
    γ * (‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      (D.chain.point i)) -
        source‖ * ‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
          (D.chain.point i).val)‖) ≤
      inner ℝ (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        (D.chain.point i)) - source)
        (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
          (D.chain.point i).val)) := by
  rw [D.first, D.spatialVector, map_smul]
  simp only [SlopeEnvelope.ExteriorPlan.spatialDirection, Cap.horizontal_horizontalAtHeight]
  have bound := radial_margin_forward_piece nonnegative small (D.lower i).property.1
    (sub_nonneg.mpr (D.forward i).le) margin
  convert bound using 1 <;>
    simp only [CompatiblePotentialRouting.terminalPoint, SlopeEnvelope.ExteriorPlan.ray,
      add_smul] <;>
    abel_nf

open Classical in
/-- The actual terminal chain begins at the literal original ray truncation point. -/
theorem CompatibleComparisonTerminalChainModel.projected_initial :
    ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain).vertex 0 =
      R.terminalPoint level r := by
  have first := D.first 0
  rw [D.start_time, add_zero] at first
  exact ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc
    D.chain 0).trans first

open Classical in
/-- Source distance increases throughout the actual outer terminal bank. -/
theorem CompatibleComparisonTerminalChainModel.projected_radialFrom
    (source : Plane) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : γ * (‖R.terminalPoint level r - source‖ *
        ‖R.exterior.direction (R.exterior.slope (R.terminalIndex r))‖) ≤
      inner ℝ (R.terminalPoint level r - source)
        (R.exterior.direction (R.exterior.slope (R.terminalIndex r)))) :
    ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain).RadialFrom source
      0 := by
  intro i _
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  have bound := D.radial_margin source nonnegative small margin i
  rw [← (NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc D.chain i,
    ← (NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_edge D.chain i] at bound
  exact (mul_nonneg nonnegative (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans bound

open Classical in
/-- The entire projected physical terminal chain is precisely the original closed ray interval. -/
theorem CompatibleComparisonTerminalChainModel.projected_carrier :
    Set.range ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain).path =
      Set.range (fun u : Set.Icc (0 : ℝ) DurationAt[later,r] =>
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + u.val)) := by
  rw [SpatialFolding.projectedBoundaryChain_path_range, ← D.trace, ← Set.range_comp]
  apply congrArg Set.range
  funext u
  exact (congrArg Cap.horizontal
    (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side u)).trans
      (SpatialEnvelope.horizontal_point M.plane _)

end Unfoldings.ConvexRoof
