module

public import Unfoldings.Roof.CompatibleSourceBankTerminalJoin
public import Unfoldings.Roof.CompatibleSourceBankTerminalGerm
public import Unfoldings.Roof.RestoredTerminalSide

/-! Actual complete source-bank endpoints recover unique original terminal side labels. -/

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

local instance sourceTerminalSideIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance sourceTerminalSideWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The true endpoint copy of a complete source bank fixes its original terminal side.
The source bank, local cut equality and side label are all derived, including the one-edge case. -/
theorem existsUnique_compatibleSourceBank_terminal_side
    (S : (Fcut).parents.ParentFrontier) {m : ℕ}
    (chain : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (source : (T).pairedComplex.Vertex Set.univ) (processed : source ∈ S.processed)
    (span : (Fcut).parents.distanceToRoot source = m + 1)
    (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] source)
    (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root source) :
    let endpoint := MapAt[S] ((T).pairedComplex.vertexPoint RetainAt[S]
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)))
    ∃! side : Bool, endpoint = K.restoredWholeTerminalBank compact nonempty R no_boundary W
      CutsAt[S] IncludedAt[S] RootAt[source,by omega] side
      ⟨R.terminalTime level RootAt[source,by omega], (R.terminalTime_pos level higher _).le⟩ := by
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
  obtain ⟨ε, radius, germ⟩ := K.exists_compatibleSourceBank_terminal_cut_germ compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S chain source processed span
    labels terminal
  exact K.existsUnique_restoredWholeTerminalBank_side_of_germ compact nonempty R no_boundary W
    CutsAt[S] IncludedAt[S] RootAt[source,by omega]
    ⟨R.terminalTime level RootAt[source,by omega], (R.terminalTime_pos level higher _).le⟩
    (R.terminalTime_pos level higher _) (MapAt[S] x)
    ((congrArg Cap.horizontal (mapped.trans physical)).trans (SpatialEnvelope.horizontal_point _ _))
    radius germ

end Unfoldings.ConvexRoof
