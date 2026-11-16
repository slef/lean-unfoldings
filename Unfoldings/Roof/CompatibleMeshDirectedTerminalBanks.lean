module

public import Unfoldings.Roof.CompatibleMeshTerminalMatching
public import Unfoldings.Roof.CompatibleTerminalDenseBankMatching
public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Metric.PositiveClosedInterval
public import Unfoldings.Geometry.SpatialEnvelopeCutDomain
public import Unfoldings.Roof.ConstructedFiniteTerminalBankMetric

/-! Actual original directed fine banks match their whole terminal banks at every parameter. -/

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

local instance directedMeshTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


variable (W : R.WholeCutModel M)

local instance directedMeshTerminalWholeFintype : Fintype W.Index := W.finiteIndex

/-- Geometric endpoints and their forward order identify an entire original directed
fine bank with a named whole terminal bank, including both actual endpoint copies. -/
theorem compatibleMesh_directedBank_wholeTerminal
    (r : {v // v ∈ R.parents.roots}) (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s < t)
    (first : Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s)
    (last : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) t) :
    ∃ side : Bool, ∀ u : unitInterval,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W ((T).pairedComplex.directedBoundaryPath p u) =
          K.wholeTerminalBank compact nonempty R no_boundary W r side
            (nonnegativeIntervalLineMap s t nonnegative forward.le u) := by
  let time := nonnegativeIntervalLineMap s t nonnegative forward.le
  apply K.wholeTerminalBank_side_of_dense_positive compact nonempty R no_boundary W r
    (fun u : unitInterval => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W ((T).pairedComplex.directedBoundaryPath p u))
    ((K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W).continuous.comp
      ((T).pairedComplex.continuous_directedBoundaryPath p))
    time (continuous_nonnegativeIntervalLineMap s t nonnegative forward.le)
    {u | 0 < u.val} (isPreconnected_positiveIcc 1) (dense_positiveIcc zero_lt_one)
  · intro u hu
    change 0 < s + u.val * (t - s)
    exact lt_of_le_of_lt nonnegative (lt_add_of_pos_right s (mul_pos hu (sub_pos.mpr forward)))
  · intro u
    have physical := congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W
      ((T).pairedComplex.directedBoundaryPath p u))
    apply physical.trans
    have interpolation := (T).pairedFolding.horizontal_directedBoundaryPath p u
    apply interpolation.trans
    rw [first, last]
    dsimp only [time, nonnegativeIntervalLineMap, SlopeEnvelope.ExteriorPlan.ray]
    rw [AffineMap.lineMap_apply_module']
    module

/-- Every forward terminal endpoint of an actual fine bank lies before the original truncation. -/
theorem compatibleMesh_directedBank_terminal_end_before
    (r : {v // v ∈ R.parents.roots}) (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    {t : ℝ} (nonnegative : 0 ≤ t)
    (last : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) t) : t ≤ R.terminalTime level r := by
  have member := (T).toTriangulation.fold_horizontal_mem_clip (Fcut).retain
    ((T).pairedComplex.vertexPoint (Fcut).retain
      ((T).pairedComplex.boundaryEndVertex (Fcut).retain
        ((T).pairedComplex.boundaryTurn (Fcut).retain p)))
  change Cap.horizontal ((T).pairedFolding.boundaryPosition
    ((T).pairedComplex.boundaryTurn (Fcut).retain p)) ∈
      SpatialEnvelope.clip M.plane (-level) at member
  have on_ray := Eq.mp (congrArg (fun z : Plane => z ∈ SpatialEnvelope.clip M.plane (-level)) last)
    member
  rw [M.clip_eq_sublevel, neg_neg] at on_ray
  exact (R.terminal_ray_sublevel_iff level higher r nonnegative).mp on_ray

/-- A genuine forward original bank is exactly the corresponding constructed finite-bank
restriction at every original parameter. Continuity retains its actual final endpoint copy. -/
theorem compatibleMesh_directedBank_finiteTerminal
    (r : {v // v ∈ R.parents.roots}) (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s < t) (before : t ≤ R.terminalTime level r)
    (first : Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s)
    (last : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) t) :
    ∃ side : Bool, ∀ u : unitInterval,
      (T).pairedComplex.directedBoundaryPath p u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side
          (closedNonnegativeIntervalLineMap s t (R.terminalTime level r)
            nonnegative forward.le before u) := by
  let time := nonnegativeIntervalLineMap s t nonnegative forward.le
  let param := closedNonnegativeIntervalLineMap s t (R.terminalTime level r)
    nonnegative forward.le before
  obtain ⟨side, matching⟩ := K.compatibleMesh_directedBank_wholeTerminal compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r p nonnegative forward first last
  let target (u : unitInterval) :=
    K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side (param u)
  have continuous_target : Continuous target :=
    (K.compatibleMeshTerminalBank_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side).continuous.comp
      (continuous_closedNonnegativeIntervalLineMap s t (R.terminalTime level r)
        nonnegative forward.le before)
  have agrees : Set.EqOn ((T).pairedComplex.directedBoundaryPath p) target
      {u : unitInterval | u.val < 1} := by
    intro u hu
    have inner_before : (time u).val < R.terminalTime level r := by
      have strict : s + u.val * (t - s) < t := by
        nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr forward)]
      exact strict.trans_le before
    have interpolation := (T).pairedFolding.horizontal_directedBoundaryPath p u
    have original_position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
        ((T).pairedComplex.directedBoundaryPath p u)) =
          R.exterior.ray (R.terminalIndex r) (time u).val := by
      apply interpolation.trans
      rw [first, last]
      dsimp only [time, nonnegativeIntervalLineMap, SlopeEnvelope.ExteriorPlan.ray]
      rw [AffineMap.lineMap_apply_module']
      module
    have source_below : (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
          ((T).pairedComplex.directedBoundaryPath p u))) < level :=
      (congrArg (K.clippedExtension slopes compact nonempty).height original_position).trans_lt
        ((R.terminal_ray_below_iff level higher r (time u).property).mpr inner_before)
    exact K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W _ source_below _
      ((matching u).trans (K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W r side (param u)).symm)
  exact ⟨side, fun u => agrees.closure ((T).pairedComplex.continuous_directedBoundaryPath p)
    continuous_target (dense_intervalBelowEnd zero_lt_one u)⟩

/-- A forward original fine bank constructs its finite terminal restriction and its exact
affine parameters. The finite endpoint bound follows from the original mesh geometry. -/
theorem exists_compatibleMesh_directedBank_terminalRestriction
    (r : {v // v ∈ R.parents.roots}) (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s < t)
    (first : Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s)
    (last : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) t) :
    ∃ side : Bool, ∃ param : unitInterval → Set.Icc (0 : ℝ) (R.terminalTime level r),
      Continuous param ∧ (∀ u, (param u).val = s + u.val * (t - s)) ∧
      ∀ u, (T).pairedComplex.directedBoundaryPath p u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side (param u) := by
  have before := K.compatibleMesh_directedBank_terminal_end_before compact nonempty R no_boundary
    level higher M positive inner_disk beta acute r p (nonnegative.trans forward.le) last
  obtain ⟨side, same⟩ := K.compatibleMesh_directedBank_finiteTerminal compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r p nonnegative forward before first last
  exact ⟨side, closedNonnegativeIntervalLineMap s t (R.terminalTime level r)
    nonnegative forward.le before, continuous_closedNonnegativeIntervalLineMap _ _ _ _ _ _,
    fun _ => rfl, same⟩

/-- The entire original fine-bank trace is the exact named finite-bank subinterval,
including its actual endpoint copies. -/
theorem compatibleMesh_directedBank_terminal_trace
    (r : {v // v ∈ R.parents.roots}) (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s < t)
    (first : Cap.horizontal ((T).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s)
    (last : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn (Fcut).retain p)) =
        R.exterior.ray (R.terminalIndex r) t) :
    ∃ side : Bool, Set.range ((T).pairedComplex.directedBoundaryPath p) =
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) '' {q | s ≤ q.val ∧ q.val ≤ t} := by
  have before := K.compatibleMesh_directedBank_terminal_end_before compact nonempty R no_boundary
    level higher M positive inner_disk beta acute r p (nonnegative.trans forward.le) last
  obtain ⟨side, same⟩ := K.compatibleMesh_directedBank_finiteTerminal compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r p nonnegative forward before first last
  let param := closedNonnegativeIntervalLineMap s t (R.terminalTime level r)
    nonnegative forward.le before
  have coverage : Set.range param = {q | s ≤ q.val ∧ q.val ≤ t} :=
    range_closedNonnegativeIntervalLineMap _ _ _ _ forward _
  refine ⟨side, Set.ext fun x => ?_⟩
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨param u, coverage.subset ⟨u, rfl⟩, (same u).symm⟩
  · rintro ⟨q, hq, equal⟩
    obtain ⟨u, at_q⟩ := coverage.symm.subset hq
    exact ⟨u, (same u).trans ((congrArg
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) at_q).trans equal)⟩

end Unfoldings.ConvexRoof
