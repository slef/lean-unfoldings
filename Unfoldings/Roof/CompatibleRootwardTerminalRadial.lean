module

public import Unfoldings.Roof.CompatibleRootwardRadialHeading
public import Unfoldings.Roof.CompatibleMeshRootwardContinuation
public import Unfoldings.Roof.CompatibleComparisonTerminalChainRadial

/-! The current original fresh source controls every actual outer terminal bank. -/

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

local instance rootwardTerminalRadialChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardTerminalRadialChartWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

local notation "SourceAt[" j "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "FrontierAt[" j "]" => TriangleComplex.contourFrontier
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)
local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "ChainAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

local notation "ImageAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[j]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side j h k hk)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

open Classical in
local instance rootwardTerminalRadialNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "StemAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- The actual current source has the same annular margin on the terminal ray at the old rim. -/
theorem compatibleMeshCurrentRootwardTerminal_source_margin
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    let root := RootAt[SourceAt[i],by omega]
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖R.terminalPoint level root - (Q).projectedVertex SourceAt[i]‖ *
        ‖R.exterior.direction (R.exterior.slope (R.terminalIndex root))‖) ≤
      inner ℝ (R.terminalPoint level root - (Q).projectedVertex SourceAt[i])
        (R.exterior.direction (R.exterior.slope (R.terminalIndex root))) := by
  have margin := K.compatibleMeshContinuedRootwardPath_source_margin compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length
    (time := 1) (by norm_num) (Fin.last (m + 1))
  rw [K.compatibleMeshContinuedRootwardPath_vertex_castSucc,
    K.compatibleMeshContinuedRootwardPath_edge_last, one_smul,
    K.compatibleMeshCurrentRootwardPath_last_terminalPoint] at margin
  exact margin

open Classical in
/-- Every actual outer bank retains the original annular source margin, at every contour stage. -/
theorem compatibleMeshCurrentRootwardComparisonTerminal_radial_margin
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) (tailSide : Bool)
    (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i] later ordered
      RootAt[SourceAt[i],by omega] tailSide) (j : Fin (D.length + 1)) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
          (D.chain.point j)) - (Q).projectedVertex SourceAt[i]‖ *
        ‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection
          (D.chain.point j).val)‖) ≤
      inner ℝ (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
        (D.chain.point j)) - (Q).projectedVertex SourceAt[i])
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection
          (D.chain.point j).val)) :=
  D.radial_margin ((Q).projectedVertex SourceAt[i]) (fine_annular_radial_margin_pos small).le
    (Real.cos_le_one _)
    (K.compatibleMeshCurrentRootwardTerminal_source_margin compact nonempty R no_boundary
      level higher
      M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length) j

end Unfoldings.ConvexRoof
