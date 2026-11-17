module

public import Unfoldings.Roof.CompatibleMeshRootwardTerminal
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.RestoredWholeTerminalBanks

/-! Actual intrinsic current rootward endpoints join constructed whole terminal-bank dilations. -/

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

local instance rootwardIntrinsicJoinIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardIntrinsicJoinWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The actual last intrinsic endpoint copy of the current rootward bank. -/
def compatibleMeshCurrentRootwardEnd
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (T).pairedComplex.Realization RetainAt[FrontierAt[i]] :=
  (T).pairedComplex.vertexPoint _ ((T).pairedComplex.boundaryEndVertex _
    ((T).pairedComplex.boundaryTurn _ (ChainAt[i,fresh,m,length]).last))

/-- The last actual intrinsic endpoint has the original full spatial terminal coordinate. -/
theorem fold_compatibleMeshCurrentRootwardEnd
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (T).pairedFolding.toSpace RetainAt[FrontierAt[i]]
      (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side i fresh m length) =
      SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[SourceAt[i],by omega]) := by
  change (T).pairedFolding.boundaryPosition
    ((T).pairedComplex.boundaryTurn _ (ChainAt[i,fresh,m,length]).last) = _
  exact ((T).pairedFolding.boundarySpatialChain_vertex_last (ChainAt[i,fresh,m,length])).symm.trans
    (K.compatibleMeshCurrentRootwardChain_last_spatial_terminalPoint compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length)

/-- The actual current rootward endpoint equals a restored original whole-bank copy at its
original terminal time. This is an equality in the intrinsic intermediate cut metric.
That same named bank is an entire constructed half-line dilation with exact spatial speed. -/
theorem exists_compatibleMeshCurrentRootwardEnd_terminal_bank
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ tailSide : Bool,
      K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W FrontierAt[i]
        (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side i fresh m length) =
      K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
        IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide
        ⟨R.terminalTime level RootAt[SourceAt[i],by omega],
          (R.terminalTime_pos level higher _).le⟩ := by
  apply K.exists_restoredWholeTerminalBank_side compact nonempty R no_boundary W
    CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega]
    ⟨R.terminalTime level RootAt[SourceAt[i],by omega], (R.terminalTime_pos level higher _).le⟩
    (R.terminalTime_pos level higher _) _
  have mapped := K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W FrontierAt[i]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length)
  have physical := K.fold_compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh m length
  exact (congrArg Cap.horizontal (mapped.trans physical)).trans
    (SpatialEnvelope.horizontal_point _ _)

/-- Construct an entire metric terminal bank joined to the actual current rootward endpoint,
with its literal original spatial coordinates and exact spatial speed at all times. -/
theorem exists_compatibleMeshCurrentRootwardEnd_terminal_dilation
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ tail : ℝ≥0 →ᵈ W.partition.Cut CutsAt[FrontierAt[i]],
      tail ⟨R.terminalTime level RootAt[SourceAt[i],by omega],
        (R.terminalTime_pos level higher _).le⟩ =
      K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W FrontierAt[i]
        (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side i fresh m length) ∧
      (∀ t, (W.partition.restoreCut CutsAt[FrontierAt[i]] (tail t)).val =
        SpatialEnvelope.point M.plane
          (R.exterior.ray (R.terminalIndex RootAt[SourceAt[i],by omega]) t.val)) ∧
      ∀ s t, edist (tail s) (tail t) =
        (‖R.exterior.spatialDirection (R.terminalIndex RootAt[SourceAt[i],by omega])‖₊ : ℝ≥0∞) *
          edist s t := by
  obtain ⟨tailSide, endpoint⟩ := K.exists_compatibleMeshCurrentRootwardEnd_terminal_bank compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  refine ⟨K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
    IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide, endpoint.symm, ?_, ?_⟩
  · exact K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
      IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide
  · exact K.edist_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
      IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide

end Unfoldings.ConvexRoof
