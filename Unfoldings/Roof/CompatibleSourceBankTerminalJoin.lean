module

public import Unfoldings.Roof.CompatibleSourceBankTerminal
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.RestoredWholeTerminalBanks

/-! Complete source-bank endpoint copies join their actual whole-cut terminal dilations. -/

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

local instance sourceBankTerminalJoinIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance sourceBankTerminalJoinWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

/-- The complete source bank joins an actual whole-cut terminal bank with exact intrinsic
speed and original spatial coordinates at every positive time. One-edge banks are included. -/
theorem exists_compatibleSourceBank_terminal_dilation
    (S : (Fcut).parents.ParentFrontier) {m : ℕ}
    (chain : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (source : (T).pairedComplex.Vertex Set.univ)
    (span : (Fcut).parents.distanceToRoot source = m + 1)
    (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] source)
    (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root source) :
    ∃ tail : ℝ≥0 →ᵈ W.partition.Cut CutsAt[S],
      tail ⟨R.terminalTime level RootAt[source,by omega],
        (R.terminalTime_pos level higher _).le⟩ =
        MapAt[S] ((T).pairedComplex.vertexPoint RetainAt[S]
          ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last))) ∧
      (∀ t, (W.partition.restoreCut CutsAt[S] (tail t)).val =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex RootAt[source,by omega])
          t.val)) ∧
      ∀ s t, edist (tail s) (tail t) =
        (‖R.exterior.spatialDirection (R.terminalIndex RootAt[source,by omega])‖₊ : ℝ≥0∞) *
          edist s t := by
  obtain ⟨d, speed, last, spatial, projected, points⟩ :=
    K.exists_compatibleSourceBank_terminal_geometry compact nonempty R no_boundary level higher M
      positive inner_disk beta acute chain source span labels terminal
  let x := (T).pairedComplex.vertexPoint RetainAt[S]
    ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last))
  have physical : (T).pairedFolding.toSpace RetainAt[S] x =
      SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[source,by omega]) :=
    ((T).pairedFolding.boundarySpatialChain_vertex_last chain).symm.trans last
  have mapped := K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S x
  obtain ⟨side, endpoint⟩ := K.exists_restoredWholeTerminalBank_side compact nonempty R no_boundary
    W CutsAt[S] IncludedAt[S] RootAt[source,by omega]
    ⟨R.terminalTime level RootAt[source,by omega], (R.terminalTime_pos level higher _).le⟩
    (R.terminalTime_pos level higher _) (MapAt[S] x)
    ((congrArg Cap.horizontal (mapped.trans physical)).trans (SpatialEnvelope.horizontal_point _ _))
  refine ⟨K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] RootAt[source,by omega] side, endpoint.symm, ?_, ?_⟩
  · exact K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S]
      IncludedAt[S] RootAt[source,by omega] side
  · exact K.edist_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S]
      IncludedAt[S] RootAt[source,by omega] side

end Unfoldings.ConvexRoof
