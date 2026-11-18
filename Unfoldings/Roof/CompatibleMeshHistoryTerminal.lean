module

public import Unfoldings.Roof.CompatibleMeshTerminalContinuation
public import Unfoldings.Roof.TerminalArrival
public import Unfoldings.Geometry.TerminalEdgeRay

/-! Every complete fine history arrives along its exact original unbounded terminal ray. -/

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

local instance compatibleHistoryTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h
local notation "HistoryAt[" s "," n "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s n

/-- Every last bank is genuine, including a one-edge source-to-rim history. -/
theorem compatibleMeshHistory_last_edge_ne_zero
    (start : (T).pairedComplex.Vertex Set.univ) (m : ℕ)
    (span : (Fcut).parents.distanceToRoot start = m + 1) :
    (HistoryAt[start,m + 1]).edge (Fin.last m) ≠ 0 := by
  intro zero
  have indices := (K.compatibleMeshHistory_vertex_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute start (m + 1) span.ge) (sub_eq_zero.mp zero)
  have values := congrArg Fin.val indices
  change m + 1 = m at values
  omega

/-- The genuine final bank reaches the named terminal point along that same original ray. -/
theorem exists_compatibleMeshHistory_terminal_arrival
    (start : (T).pairedComplex.Vertex Set.univ) (m : ℕ)
    (span : (Fcut).parents.distanceToRoot start = m + 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s < R.terminalTime level RootAt[start,by omega] ∧
      (HistoryAt[start,m + 1]).vertex (Fin.last m).castSucc =
        R.exterior.ray (R.terminalIndex RootAt[start,by omega]) s := by
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute start (m + 1) (by omega) span
  have step := K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start (m + 1) span.ge (Fin.last m)
  rw [Fin.succ_last, last] at step
  apply K.followsStep_to_terminalPoint compact nonempty R no_boundary level higher
    RootAt[start,by omega] step
  intro same
  apply K.compatibleMeshHistory_last_edge_ne_zero compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start m span
  simp only [PolygonalChain.edge, Fin.succ_last, last, same, sub_self]

/-- Continuing the actual last edge introduces no turn at the original truncation point. -/
theorem exists_compatibleMeshHistory_last_edge_direction
    (start : (T).pairedComplex.Vertex Set.univ) (m : ℕ)
    (span : (Fcut).parents.distanceToRoot start = m + 1) :
    ∃ d : ℝ, 0 < d ∧ (HistoryAt[start,m + 1]).edge (Fin.last m) =
      d • R.exterior.direction (R.exterior.slope (R.terminalIndex RootAt[start,by omega])) := by
  obtain ⟨s, nonnegative, before, first⟩ := K.exists_compatibleMeshHistory_terminal_arrival compact
    nonempty R no_boundary level higher M positive inner_disk beta acute start m span
  refine ⟨R.terminalTime level RootAt[start,by omega] - s, sub_pos.mpr before, ?_⟩
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute start (m + 1) (by omega) span
  rw [PolygonalChain.edge, Fin.succ_last, last, first]
  change R.exterior.ray _ _ - R.exterior.ray _ s = _
  simp only [SlopeEnvelope.ExteriorPlan.ray]
  module

/-- The complete extrapolated last-edge bank is the original terminal ray with its exact
positive physical speed. No extra corner or substituted ray is introduced. -/
theorem exists_compatibleMeshHistory_terminal_ray
    (start : (T).pairedComplex.Vertex Set.univ) (m : ℕ)
    (span : (Fcut).parents.distanceToRoot start = m + 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ≥0,
      (HistoryAt[start,m + 1]).terminalEdgeRay.tail t =
        R.exterior.ray (R.terminalIndex RootAt[start,by omega])
          (R.terminalTime level RootAt[start,by omega] + d * t.val) := by
  obtain ⟨d, positive_speed, direction⟩ := K.exists_compatibleMeshHistory_last_edge_direction
    compact nonempty R no_boundary level higher M positive inner_disk beta acute start m span
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute start (m + 1) (by omega) span
  refine ⟨d, positive_speed, fun t => ?_⟩
  change (HistoryAt[start,m + 1]).vertex (Fin.last (m + 1)) +
    t.val • (HistoryAt[start,m + 1]).edge (Fin.last m) = _
  rw [last, direction]
  simp only [CompatiblePotentialRouting.terminalPoint, SlopeEnvelope.ExteriorPlan.ray]
  module

/-- The entire continued physical carrier is the genuine original tail beyond the rim,
including its junction point, for every nonempty original fine history. -/
theorem compatibleMeshHistory_terminal_carrier
    (start : (T).pairedComplex.Vertex Set.univ) (m : ℕ)
    (span : (Fcut).parents.distanceToRoot start = m + 1) :
    (HistoryAt[start,m + 1]).terminalEdgeRay.carrier =
      Set.range (HistoryAt[start,m + 1]).path ∪
        Set.range (fun u : ℝ≥0 => R.exterior.ray (R.terminalIndex RootAt[start,by omega])
          (R.terminalTime level RootAt[start,by omega] + u.val)) := by
  obtain ⟨d, speed, position⟩ := K.exists_compatibleMeshHistory_terminal_ray compact nonempty R
    no_boundary level higher M positive inner_disk beta acute start m span
  apply congrArg (fun tail => Set.range (HistoryAt[start,m + 1]).path ∪ tail)
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨d * t.val, mul_nonneg speed.le t.coe_nonneg⟩, (position t).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨⟨u.val / d, div_nonneg u.coe_nonneg speed.le⟩, ?_⟩
    erw [position]
    congr 1
    dsimp only
    field_simp [speed.ne']

end Unfoldings.ConvexRoof
