module

public import Unfoldings.Roof.CompatibleRootwardJunctionGerm
public import Unfoldings.Roof.RestoredTerminalHalfplane
public import Unfoldings.Metric.PlacedBallCenterTransport

/-! Whole original halfplane neighborhoods at actual intrinsic rootward terminal junctions. -/

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

local instance rootwardJunctionChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardJunctionChartWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The actual intrinsic current rootward endpoint has a whole halfplane neighborhood in
its original supporting frame. The truncation join creates no new geometric corner.
Both the terminal side and the chart are constructed from the original current bank. -/
theorem exists_compatibleMeshCurrentRootwardEnd_halfplane_chart
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    let root := RootAt[SourceAt[i],by omega]
    let endpoint := ImageAt[i,fresh,m,length]
    ∃ tailSide : Bool, ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace
        ((W.terminalSupportCells root).anchor tailSide)
        (orientMap (R.exterior.point (R.terminalIndex root))
          (R.exterior.ray (R.terminalIndex root) 1))
        (W.terminalSigns root),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells root).anchor tailSide))).project.symm
          (R.terminalPoint level root) ∧
        ∃ D : Metric.eball endpoint (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support
            ((W.terminalSupportCells root).anchor tailSide))).place
              (D y).val.val = (W.partition.restoreCut CutsAt[FrontierAt[i]] y.val).val := by
  dsimp only
  obtain ⟨tailSide, endpoint⟩ := K.exists_compatibleMeshCurrentRootwardEnd_terminal_bank compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  obtain ⟨δ, radius_positive, germ⟩ := K.exists_compatibleMeshCurrentRootwardEnd_cut_germ compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  obtain ⟨ε, εpos, a, center, D, agrees⟩ :=
    K.exists_restoredWholeTerminalBank_halfplane_chart compact nonempty R no_boundary W
      CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide
      ⟨R.terminalTime level RootAt[SourceAt[i],by omega], (R.terminalTime_pos level higher _).le⟩
      (R.terminalTime_pos level higher _) radius_positive germ
  refine ⟨tailSide, ?_⟩
  exact exists_placed_ball_chart_of_eq
    (fun z => (W.partition.restoreCut CutsAt[FrontierAt[i]] z).val)
    (fun z => (M.plane (W.partition.support
      ((W.terminalSupportCells RootAt[SourceAt[i],by omega]).anchor tailSide))).place z.val)
    (fun a => a.val = (M.plane (W.partition.support
      ((W.terminalSupportCells RootAt[SourceAt[i],by omega]).anchor tailSide))).project.symm
        (R.terminalPoint level RootAt[SourceAt[i],by omega])) endpoint
    ⟨ε, εpos, a, center, D, agrees⟩

end Unfoldings.ConvexRoof
