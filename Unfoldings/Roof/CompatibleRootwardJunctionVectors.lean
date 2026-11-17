module

public import Unfoldings.Roof.CompatibleRootwardJunctionGerm
public import Unfoldings.Roof.CompatibleMeshRootwardContinuation

/-! Actual final rootward bank vectors agree exactly with their unbounded terminal continuations. -/

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

local instance rootwardJunctionVectorIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardJunctionVectorWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The final actual projected bank is a positive multiple of the original terminal
ray direction. Truncation creates no turn in the original physical path. -/
theorem exists_compatibleMeshCurrentRootwardPath_last_edge_direction
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ d : ℝ, 0 < d ∧ (PathAt[i,fresh,m,length]).edge (Fin.last m) =
      d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[SourceAt[i],by omega]))
        := by
  obtain ⟨s, nonnegative, before, first⟩ :=
    K.exists_compatibleMeshCurrentRootwardPath_terminal_arrival compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length
  refine ⟨R.terminalTime level RootAt[SourceAt[i],by omega] - s, sub_pos.mpr before, ?_⟩
  rw [PolygonalChain.edge, Fin.succ_last,
    K.compatibleMeshCurrentRootwardPath_last_terminalPoint, first]
  change R.exterior.ray _ _ - R.exterior.ray _ s = _
  simp only [SlopeEnvelope.ExteriorPlan.ray]
  module

/-- The final physical bank has the exact full spatial terminal direction, including
height, with the same positive duration as its projected final bank. -/
theorem exists_compatibleMeshCurrentRootwardChain_last_edge_spatialDirection
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ d : ℝ, 0 < d ∧
      ((T).pairedFolding.boundarySpatialChain (ChainAt[i,fresh,m,length])).edge (Fin.last m) =
        d • R.exterior.spatialDirection (R.terminalIndex RootAt[SourceAt[i],by omega]) ∧
      (PathAt[i,fresh,m,length]).edge (Fin.last m) =
        d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[SourceAt[i],by
          omega])) := by
  obtain ⟨s, nonnegative, before, first⟩ :=
    K.exists_compatibleMeshCurrentRootwardPath_terminal_arrival compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length
  let d := R.terminalTime level RootAt[SourceAt[i],by omega] - s
  have projected : (PathAt[i,fresh,m,length]).edge (Fin.last m) =
      d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[SourceAt[i],by omega]))
        := by
    rw [PolygonalChain.edge, Fin.succ_last,
      K.compatibleMeshCurrentRootwardPath_last_terminalPoint, first]
    change R.exterior.ray _ _ - R.exterior.ray _ s = _
    simp only [SlopeEnvelope.ExteriorPlan.ray]
    module
  refine ⟨d, sub_pos.mpr before, ?_, projected⟩
  rw [PolygonalChain.edge, Fin.succ_last,
    K.compatibleMeshCurrentRootwardChain_last_spatial_terminalPoint,
    (T).toTriangulation.boundarySpatialChain_vertex_eq_graph]
  change SpatialEnvelope.point M.plane (R.exterior.ray _ _) -
    SpatialEnvelope.point M.plane ((PathAt[i,fresh,m,length]).vertex (Fin.last m).castSucc) = _
  rw [first]
  exact R.exterior.spatial_ray_sub M _ (R.terminalTime_pos level higher _).le nonnegative

end Unfoldings.ConvexRoof
