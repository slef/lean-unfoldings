module

public import Unfoldings.Roof.CompatibleRootwardIntrinsicPath
public import Unfoldings.Roof.CompatibleProcessedComparisonPaths

/-! Place original rootward stems and arbitrary finite tails in larger comparison meshes. -/

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

local instance rootwardComparisonLiftIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonLiftWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "MapAt[" j "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W FrontierAt[j]
local notation "EndAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "StartAt[" j "," h "," k "," hk "]" =>
  TriangleComplex.vertexPoint
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) _
    (TriangleComplex.boundaryEndVertex
      (SpatialEnvelope.Triangulation.pairedComplex
        (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) _
      (PairedInvolutions.System.Chain.first (ChainAt[j,h,k,hk])))

open Classical in
/-- Every finite portion of the full original rootward bank has an actual continuous copy
in a constructed larger comparison mesh of the same intermediate cut. The original whole stem
and arbitrary terminal interval are retained, point for point and with their entire carrier.
No outer height bound, comparison mesh, bank label or metric certificate is supplied. -/
theorem exists_compatibleMeshRootward_comparison_path
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ≥0) :
    let root := RootAt[SourceAt[i],by omega]
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher _).le⟩
    ∃ tailSide : Bool, ∃ P : Path (MapAt[i] StartAt[i,fresh,m,length])
      (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
        IncludedAt[FrontierAt[i]] root tailSide (initial + time)),
      Set.range P = MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) ∪
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
          IncludedAt[FrontierAt[i]] root tailSide) '' Set.Icc initial (initial + time) ∧
      ∃ later : ℝ, ∃ ordered : level < later,
        ∃ below : ∀ t, (K.clippedExtension slopes compact nonempty).height
          (Cap.horizontal (W.partition.restoreCut CutsAt[FrontierAt[i]] (P t)).val) < later,
        ∃ Pfine : Path
            (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
              positive inner_disk beta acute W FrontierAt[i] later ordered (P 0) (below 0))
            (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
              positive inner_disk beta acute W FrontierAt[i] later ordered (P 1) (below 1)),
          (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W FrontierAt[i] later ordered) '' Set.range Pfine =
              Set.range P ∧
          ∀ t, K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
            higher M positive inner_disk beta acute W FrontierAt[i] later ordered (Pfine t) =
              P t := by
  dsimp only
  obtain ⟨tailSide, P, carrier, _intersection⟩ :=
    K.exists_compatibleMeshCurrentRootward_terminal_path compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side i fresh m length time
  obtain ⟨later, ordered, below, Pfine, pointwise⟩ :=
    K.exists_compatibleMeshProcessedComparison_path compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i] P
  refine ⟨tailSide, P, carrier, later, ordered, below, Pfine, ?_, pointwise⟩
  exact image_range_eq_of_pointwise _ _ P pointwise

end Unfoldings.ConvexRoof
