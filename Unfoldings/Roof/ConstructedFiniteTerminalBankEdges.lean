module

public import Unfoldings.Roof.ConstructedFiniteTerminalBoundary
public import Unfoldings.Roof.ConstructedFiniteTerminalVertices
public import Unfoldings.Roof.CompatibleMeshTerminalAlignment
public import Unfoldings.Roof.CompatibleMeshDirectedTerminalBanks
public import Unfoldings.Topology.ClosedIntervalFiniteExceptions

/-! Recover actual forward fine-bank pieces of either constructed finite terminal bank. -/

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

local instance finiteTerminalEdgesIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance finiteTerminalEdgesWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- A nonvertex terminal-bank point has strictly positive original ray time. -/
theorem compatibleMeshTerminalBank_time_pos_of_nonvertex (t : Set.Icc (0 : ℝ) τ)
    (regular : ∀ v : (T).pairedComplex.Vertex (Fcut).retain,
      K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side t ≠ (T).pairedComplex.vertexPoint (Fcut).retain v) : 0 < t.val := by
  by_contra not_positive
  have zero : t = ⟨0, le_rfl, (R.terminalTime_pos level higher r).le⟩ :=
    Subtype.ext (le_antisymm (not_lt.mp not_positive) t.property.1)
  have at_zero := K.vertexPoint_compatibleMeshTerminalStartVertex compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side
  exact regular _ ((congrArg (K.compatibleMeshTerminalBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side) zero).trans at_zero.symm)

/-- Every nonvertex point of a chosen finite terminal bank lies on an original forward bank
whose entire intrinsic path is exactly a subinterval of that same chosen bank. All endpoint
bounds, the direction and the side label are derived from the original cut geometry. -/
theorem exists_forwardDirectedBank_at_compatibleMeshTerminalBank (t : Set.Icc (0 : ℝ) τ)
    (regular : ∀ v : (T).pairedComplex.Vertex (Fcut).retain,
      K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side t ≠ (T).pairedComplex.vertexPoint (Fcut).retain v) :
    ∃ (p : (T).pairedComplex.BoundaryEnd (Fcut).retain) (s z : Set.Icc (0 : ℝ) τ)
      (forward : s.val < z.val),
      Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
        R.exterior.ray (R.terminalIndex r) s.val ∧
      Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
          R.exterior.ray (R.terminalIndex r) z.val ∧
      (∃ u : unitInterval, (T).pairedComplex.directedBoundaryPath p u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side t) ∧
      ∀ u : unitInterval, (T).pairedComplex.directedBoundaryPath p u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side
          (closedNonnegativeIntervalLineMap s.val z.val τ
            s.property.1 forward.le z.property.2 u) := by
  obtain ⟨i, u, at_point⟩ := K.exists_originalDirectedBank_at_compatibleMeshTerminalBank compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side t
  let contour := K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher M
    positive inner_disk beta acute
  let p := contour.cycle.point i
  have regular_p : ∀ v : (T).pairedComplex.Vertex (Fcut).retain,
      (T).pairedComplex.directedBoundaryPath p u ≠ (T).pairedComplex.vertexPoint (Fcut).retain v :=
    fun v equal => regular v (at_point.symm.trans equal)
  have position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
      ((T).pairedComplex.directedBoundaryPath p u)) =
        R.exterior.ray (R.terminalIndex r) t.val := by
    rw [at_point, K.fold_compatibleMeshTerminalBank]
    exact SpatialEnvelope.horizontal_point M.plane _
  have member : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
      ((T).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
    rw [position]
    exact R.terminal_ray_mem_segment level higher r t
  obtain ⟨q, s, z, forward, first, last, v, contact⟩ :=
    K.exists_compatibleMesh_forward_terminal_bank compact nonempty R no_boundary level higher M
      positive inner_disk r p u regular_p member
  have contact_copy := contact.trans at_point
  obtain ⟨found_side, same⟩ := K.compatibleMesh_directedBank_finiteTerminal compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r q s.property.1 forward
    z.property.2 first last
  have chosen_side : side = found_side := by
    by_contra different
    exact K.compatibleMeshTerminalBank_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side found_side different t _
      (K.compatibleMeshTerminalBank_time_pos_of_nonvertex compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W r side t regular)
      (contact_copy.symm.trans (same v))
  subst found_side
  exact ⟨q, s, z, forward, first, last, ⟨v, contact_copy⟩, same⟩

/-- Original forward bank ends whose entire intrinsic paths are exact subintervals of
this chosen finite terminal bank. The set is finite because the original boundary is finite. -/
def compatibleMeshTerminalBankEnds : Set ((T).pairedComplex.BoundaryEnd (Fcut).retain) :=
  {p | ∃ (s z : Set.Icc (0 : ℝ) τ) (forward : s.val < z.val),
    Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s.val ∧
    Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) z.val ∧
    ∀ u : unitInterval, (T).pairedComplex.directedBoundaryPath p u =
      K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side
        (closedNonnegativeIntervalLineMap s.val z.val τ s.property.1 forward.le z.property.2 u)}

/-- Every original terminal-bank point, including every subdivision vertex and both endpoints,
is covered by a whole original forward fine bank on its chosen side. -/
theorem compatibleMeshTerminalBank_range_eq_union_directedBanks :
    Set.range (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) =
      ⋃ p : K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side,
          Set.range ((T).pairedComplex.directedBoundaryPath p.val) := by
  let curve := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side
  let ends := K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side
  let pieces := ⋃ p : ends, Set.range ((T).pairedComplex.directedBoundaryPath p.val)
  have closed : IsClosed pieces := isClosed_iUnion_of_finite
    (fun p : ends => (isCompact_range ((T).pairedComplex.continuous_directedBoundaryPath
      p.val)).isClosed)
  have vertex_times :
      {t | curve t ∈ Set.range ((T).pairedComplex.vertexPoint (Fcut).retain)}.Finite :=
    Set.Finite.preimage (K.compatibleMeshTerminalBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side).injective.injOn
      (Set.finite_range _)
  have exceptions : {t | curve t ∉ pieces}.Finite := vertex_times.subset (by
    intro t missing
    by_contra regular
    have nonvertex : ∀ v : (T).pairedComplex.Vertex (Fcut).retain,
        curve t ≠ (T).pairedComplex.vertexPoint (Fcut).retain v :=
      fun v same => regular ⟨v, same.symm⟩
    obtain ⟨p, s, z, forward, first, last, ⟨u, contact⟩, entire⟩ :=
      K.exists_forwardDirectedBank_at_compatibleMeshTerminalBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W r side t nonvertex
    exact missing (Set.mem_iUnion.mpr
      ⟨⟨p, s, z, forward, first, last, entire⟩, u, contact⟩))
  have covered := continuous_Icc_mem_closed_of_finite_exceptions
    (R.terminalTime_pos level higher r) curve
    (K.compatibleMeshTerminalBank_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side).continuous closed exceptions
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact covered t
  · intro x member
    obtain ⟨p, u, rfl⟩ := Set.mem_iUnion.mp member
    obtain ⟨s, z, forward, _, _, entire⟩ := p.property
    exact ⟨_, (entire u).symm⟩

end Unfoldings.ConvexRoof
