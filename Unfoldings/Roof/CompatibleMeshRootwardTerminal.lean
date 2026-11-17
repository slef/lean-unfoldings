module

public import Unfoldings.Roof.CompatibleMeshRootwardGeometry
public import Unfoldings.Roof.CompatibleMeshTerminalRoot
public import Unfoldings.Roof.SpatialEnvelopeFoldingGraph

/-! Actual rootward stems join their derived original terminal rays at exact spatial points. -/

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

local instance rootwardTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardTerminalWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The actual stem ends at its uniquely derived original terminal ray, including its
original rim copy's exact coordinate. The ray need not be the contour's anchoring ray. -/
theorem compatibleMeshCurrentRootwardPath_last_terminalPoint
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (PathAt[i,fresh,m,length]).vertex (Fin.last (m + 1)) =
      R.terminalPoint level RootAt[SourceAt[i],by omega] := by
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute SourceAt[i] (m + 2) (by omega) length
  have interval := congrArg (fun P : PolygonalChain Plane (m + 1) =>
    P.vertex (Fin.last (m + 1)))
    (K.compatibleMeshCurrentRootwardPath_eq_history compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length)
  apply interval.trans
  apply Eq.trans ?_ last
  change (HistoryAt[i,m]).vertex ⟨1 + (m + 1), by omega⟩ =
    (HistoryAt[i,m]).vertex (Fin.last (m + 2))
  congr 1
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- The original physical stem joins that same ray on the whole spatial roof,
retaining all three coordinates rather than just its horizontal projection. -/
theorem compatibleMeshCurrentRootwardChain_last_spatial_terminalPoint
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ((T).pairedFolding.boundarySpatialChain
      (K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side i fresh m length)).vertex (Fin.last (m + 1)) =
      SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[SourceAt[i],by omega]) := by
  have graph := (T).toTriangulation.boundarySpatialChain_vertex_eq_graph
    (K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length) (Fin.last (m + 1))
  exact graph.trans (congrArg (SpatialEnvelope.point M.plane)
    (K.compatibleMeshCurrentRootwardPath_last_terminalPoint compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length))

end Unfoldings.ConvexRoof
