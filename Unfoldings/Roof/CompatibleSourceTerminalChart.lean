module

public import Unfoldings.Roof.CompatibleSourceTerminalSide
public import Unfoldings.Roof.RestoredTerminalHalfplane
public import Unfoldings.Metric.PlacedBallCenterTransport

/-! Complete source-bank endpoints have actual original half-plane metric neighborhoods. -/

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

local instance sourceTerminalChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance sourceTerminalChartWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The truncation join of every complete source bank has its original whole half-plane
chart, with the actual support frame and endpoint copy. The one-edge source case is included. -/
theorem exists_compatibleSourceBank_terminal_halfplane_chart
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
    let root := RootAt[source,by omega]
    let endpoint := MapAt[S] ((T).pairedComplex.vertexPoint RetainAt[S]
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)))
    ∃ side : Bool, ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells root).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex root))
          (R.exterior.ray (R.terminalIndex root) 1)) (W.terminalSigns root),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells root).anchor side))).project.symm (R.terminalPoint level root) ∧
        ∃ D : Metric.eball endpoint (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells root).anchor side))).place
            (D y).val.val = (W.partition.restoreCut CutsAt[S] y.val).val := by
  dsimp only
  obtain ⟨side, endpoint_eq, unique_side⟩ := K.existsUnique_compatibleSourceBank_terminal_side
    compact nonempty R no_boundary level higher M positive inner_disk beta acute W S chain
    source processed span labels terminal
  obtain ⟨δ, radius, germ⟩ := K.exists_compatibleSourceBank_terminal_cut_germ compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S chain source processed span
    labels terminal
  obtain ⟨ε, positive_radius, a, center, D, agrees⟩ :=
    K.exists_restoredWholeTerminalBank_halfplane_chart compact nonempty R no_boundary W
      CutsAt[S] IncludedAt[S] RootAt[source,by omega] side
      ⟨R.terminalTime level RootAt[source,by omega], (R.terminalTime_pos level higher _).le⟩
      (R.terminalTime_pos level higher _) radius germ
  refine ⟨side, ?_⟩
  exact exists_placed_ball_chart_of_eq
    (fun z => (W.partition.restoreCut CutsAt[S] z).val)
    (fun z => (M.plane (W.partition.support
      ((W.terminalSupportCells RootAt[source,by omega]).anchor side))).place z.val)
    (fun a => a.val = (M.plane (W.partition.support
      ((W.terminalSupportCells RootAt[source,by omega]).anchor side))).project.symm
        (R.terminalPoint level RootAt[source,by omega])) endpoint_eq
    ⟨ε, positive_radius, a, center, D, agrees⟩

end Unfoldings.ConvexRoof
