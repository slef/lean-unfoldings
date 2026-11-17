module

public import Unfoldings.Roof.CompatibleRootwardJunctionChart
public import Unfoldings.Roof.CompatibleComparisonPlacedCharts

/-! Original junction halfplanes in actual larger comparison meshes. -/

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

local instance comparisonJunctionChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance comparisonJunctionChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance comparisonJunctionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

/-- The actual current terminal junction has exactly its original truncation height. -/
theorem compatibleMeshCurrentRootwardEnd_height
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[FrontierAt[i]]
        ImageAt[i,fresh,m,length]).val) = level := by
  have physical := (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W FrontierAt[i]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length)).trans
        (K.fold_compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W r side i fresh m length)
  have projected := (congrArg Cap.horizontal physical).trans (SpatialEnvelope.horizontal_point _ _)
  exact (congrArg (K.clippedExtension slopes compact nonempty).height projected).trans
    (R.terminalPoint_level level higher _)

open Classical in
/-- The actual original junction copy in the constructed larger comparison mesh. -/
@[macro_inline] def compatibleMeshCurrentRootwardComparisonJunction
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Realization
      NewRetainAt[FrontierAt[i],later,ordered] :=
  K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[i] later ordered ImageAt[i,fresh,m,length]
    ((K.compatibleMeshCurrentRootwardEnd_height compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length).trans_lt ordered)

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl

open Classical in
/-- The lifted original terminal junction has its whole original halfplane neighborhood in
every larger comparison mesh. The original side, supporting frame and spatial placement are
retained; no artificial rim angle or caller-supplied fan identification appears. -/
theorem exists_compatibleMeshCurrentRootwardComparisonJunction_halfplane_chart
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    let root := RootAt[SourceAt[i],by omega]
    ∃ tailSide : Bool, ∃ radius : ℝ, ∃ radius_positive : 0 < radius,
      ∃ a : W.partition.faceSideHalfspace
        ((W.terminalSupportCells root).anchor tailSide)
        (orientMap (R.exterior.point (R.terminalIndex root))
          (R.exterior.ray (R.terminalIndex root) 1)) (W.terminalSigns root),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells root).anchor tailSide))).project.symm
          (R.terminalPoint level root) ∧
        ∃ D : Metric.eball JunctionAt[i,fresh,m,length,later,ordered]
            (ENNReal.ofReal radius) ≃ᵢ Metric.ball a radius,
          (D ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_positive)⟩).val = a ∧
          ∀ y, (M.plane (W.partition.support
            ((W.terminalSupportCells root).anchor tailSide))).place (D y).val.val =
              (NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
                NewRetainAt[FrontierAt[i],later,ordered] y.val := by
  dsimp only
  obtain ⟨tailSide, σ, σpos, a, coordinates, H, agrees_H⟩ :=
    K.exists_compatibleMeshCurrentRootwardEnd_halfplane_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length
  let root := RootAt[SourceAt[i],by omega]
  let endpoint := ImageAt[i,fresh,m,length]
  let support := M.plane (W.partition.support ((W.terminalSupportCells root).anchor tailSide))
  let place : W.partition.faceSideHalfspace ((W.terminalSupportCells root).anchor tailSide)
      (orientMap (R.exterior.point (R.terminalIndex root))
        (R.exterior.ray (R.terminalIndex root) 1)) (W.terminalSigns root) → Space :=
    fun z => support.place z.val
  have injective : Function.Injective place := fun z w same =>
    Subtype.ext (support.place.injective same)
  have physical : (W.partition.restoreCut CutsAt[FrontierAt[i]] endpoint).val =
      SpatialEnvelope.point M.plane (R.terminalPoint level root) :=
    (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i]
      (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side i fresh m length)).trans
      (K.fold_compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side i fresh m length)
  have model_place : place a = (W.partition.restoreCut CutsAt[FrontierAt[i]] endpoint).val := by
    apply Eq.trans _ physical.symm
    exact (congrArg support.place coordinates).trans
      (SpatialEnvelope.point_eq_place M.plane
        (W.partition.support ((W.terminalSupportCells root).anchor tailSide))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex root)
          ((W.terminalSupportCells root).anchor tailSide) (W.terminalSupportCells root).threshold
          ((W.terminalSupportCells root).tail tailSide) (R.terminalTime level root)
          (R.terminalTime_pos level higher root).le)).symm
  have below := (K.compatibleMeshCurrentRootwardEnd_height compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh m length).trans_lt ordered
  obtain ⟨radius, positive_radius, D, center, agrees⟩ :=
    K.exists_compatibleMeshProcessedComparison_placed_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered endpoint below
      place injective a model_place ⟨σ, σpos, H, agrees_H⟩
  exact ⟨tailSide, radius, positive_radius, a, coordinates, D, center, agrees⟩

end Unfoldings.ConvexRoof
