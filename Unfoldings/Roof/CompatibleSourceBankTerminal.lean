module

public import Unfoldings.Roof.CompatibleSourceBankGeometry
public import Unfoldings.Roof.CompatibleMeshHistoryTerminal
public import Unfoldings.Roof.SpatialEnvelopeFoldingGraph
public import Unfoldings.Convex.ExteriorSpatialRays

/-! Complete source banks continue along the exact original spatial terminal rays. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance compatibleSourceTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

/-- The actual last bank, its spatial endpoint and its entire extrapolated tail agree
with one original terminal ray at the same positive speed, including one-edge source banks. -/
theorem exists_compatibleSourceBank_terminal_geometry
    {retain : Set (T).pairedComplex.Seam} {m : ℕ}
    (chain : ((T).pairedComplex.boundarySystem retain).Chain m)
    (source : (T).pairedComplex.Vertex Set.univ)
    (span : (Fcut).parents.distanceToRoot source = m + 1)
    (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] source)
    (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root source) :
    ∃ d : ℝ, 0 < d ∧
      ((T).pairedFolding.boundarySpatialChain chain).vertex (Fin.last (m + 1)) =
        SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[source,by omega]) ∧
      ((T).pairedFolding.boundarySpatialChain chain).edge (Fin.last m) =
        d • R.exterior.spatialDirection (R.terminalIndex RootAt[source,by omega]) ∧
      ((T).pairedFolding.projectedBoundaryChain chain).edge (Fin.last m) =
        d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[source,by omega])) ∧
      ∀ t : ℝ≥0, ((T).pairedFolding.boundarySpatialChain chain).terminalEdgeRay.tail t =
        SpatialEnvelope.point M.plane
          (R.exterior.ray (R.terminalIndex RootAt[source,by omega])
            (R.terminalTime level RootAt[source,by omega] + d * t.val)) := by
  have geometry := K.compatibleSourceBankChain_eq_history compact nonempty R no_boundary level
    higher M positive inner_disk beta acute chain source span labels terminal
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute source (m + 1) (by omega) span
  rw [← geometry] at last
  obtain ⟨s, nonnegative, before, first⟩ := K.exists_compatibleMeshHistory_terminal_arrival compact
    nonempty R no_boundary level higher M positive inner_disk beta acute source m span
  rw [← geometry] at first
  let d := R.terminalTime level RootAt[source,by omega] - s
  have speed : 0 < d := sub_pos.mpr before
  have spatial_last := (T).toTriangulation.boundarySpatialChain_vertex_eq_graph chain
    (Fin.last (m + 1))
  change ((T).pairedFolding.boundarySpatialChain chain).vertex (Fin.last (m + 1)) =
    SpatialEnvelope.point M.plane
      (((T).pairedFolding.projectedBoundaryChain chain).vertex (Fin.last (m + 1))) at spatial_last
  rw [last] at spatial_last
  have projected : ((T).pairedFolding.projectedBoundaryChain chain).edge (Fin.last m) =
      d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[source,by omega])) := by
    rw [PolygonalChain.edge, Fin.succ_last, last, first]
    simp only [CompatiblePotentialRouting.terminalPoint, SlopeEnvelope.ExteriorPlan.ray, d]
    module
  have spatial : ((T).pairedFolding.boundarySpatialChain chain).edge (Fin.last m) =
      d • R.exterior.spatialDirection (R.terminalIndex RootAt[source,by omega]) := by
    rw [PolygonalChain.edge, Fin.succ_last, spatial_last,
      (T).toTriangulation.boundarySpatialChain_vertex_eq_graph]
    change SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[source,by omega]) -
      SpatialEnvelope.point M.plane
        (((T).pairedFolding.projectedBoundaryChain chain).vertex (Fin.last m).castSucc) = _
    rw [first]
    exact R.exterior.spatial_ray_sub M _ (R.terminalTime_pos level higher _).le nonnegative
  refine ⟨d, speed, spatial_last, spatial, projected, fun t => ?_⟩
  change ((T).pairedFolding.boundarySpatialChain chain).vertex (Fin.last (m + 1)) +
    t.val • ((T).pairedFolding.boundarySpatialChain chain).edge (Fin.last m) = _
  rw [spatial_last, spatial]
  simp only [CompatiblePotentialRouting.terminalPoint]
  erw [R.exterior.spatial_point_ray M _ (R.terminalTime_pos level higher _).le,
    R.exterior.spatial_point_ray M _
      (add_nonneg (R.terminalTime_pos level higher _).le (mul_nonneg speed.le t.coe_nonneg))]
  have affine (p v : Space) (r c q : ℝ) :
      p + r • v + q • (c • v) = p + (r + c * q) • v := by module
  exact affine _ _ _ _ _

end Unfoldings.ConvexRoof
