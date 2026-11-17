module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankChains
public import Unfoldings.Complex.IntervalBoundaryChainParameters
public import Unfoldings.Polyhedron.BoundaryChainGeometry

/-! Exact original ray times and physical coordinates of the constructed terminal chains. -/

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

local instance finiteTerminalParametersIndexFintype : Fintype (T).Index :=
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

local instance finiteTerminalParametersWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- Recover exact increasing terminal times for a specified original chain on the chosen
bank, retaining both named original endpoint copies. -/
theorem parameterize_compatibleMeshTerminalBank_chain {n : ℕ}
    (chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n)
    (selected : ∀ i, chain.point i ∈
      K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)
    (source : (T).pairedComplex.boundaryEndVertex (Fcut).retain chain.first =
      K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)
    (finish : (T).pairedComplex.boundaryEndVertex (Fcut).retain
      ((T).pairedComplex.boundaryTurn (Fcut).retain chain.last) =
        K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side) :
    ∃ time : Fin (n + 2) → Set.Icc (0 : ℝ) τ, ∃ increasing : StrictMono time,
      (time 0).val = 0 ∧ (time (Fin.last (n + 1))).val = τ ∧
      ∀ (i : Fin (n + 1)) (u : unitInterval),
        (T).pairedComplex.directedBoundaryPath (chain.point i) u =
          K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W r side
            (closedNonnegativeIntervalLineMap (time i.castSucc).val (time i.succ).val τ
              (time i.castSucc).property.1
              (increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
              (time i.succ).property.2 u) := by
  classical
  let curve := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side
  have injective : Function.Injective curve :=
    (K.compatibleMeshTerminalBank_isClosedEmbedding compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side).injective
  have choices (i : Fin (n + 1)) := selected i
  choose lower upper forward first last matching using choices
  have exact_match (i) (u) : (T).pairedComplex.directedBoundaryPath (chain.point i) u = curve
      (closedNonnegativeIntervalLineMap (lower i).val (upper i).val τ
        (lower i).property.1 (forward i).le (upper i).property.2 u) :=
    matching i u
  let time := TriangleComplex.boundaryChainIntervalTime lower upper
  have increasing : StrictMono time := (T).pairedComplex.strictMono_boundaryChainIntervalTime
    chain lower upper forward curve injective exact_match
  have edge_start (i : Fin (n + 1)) : time i.castSucc = lower i :=
    TriangleComplex.boundaryChainIntervalTime_castSucc lower upper i
  have edge_finish (i : Fin (n + 1)) : time i.succ = upper i :=
    (T).pairedComplex.boundaryChainIntervalTime_succ chain lower upper forward curve injective
      exact_match i
  have initial := exact_match 0 0
  rw [closedIntervalLineMap_zero, (T).pairedComplex.directedBoundaryPath_zero] at initial
  have terminal := exact_match (Fin.last n) 1
  rw [closedIntervalLineMap_one, (T).pairedComplex.directedBoundaryPath_one] at terminal
  have zero_time : (time 0).val = 0 := by
    have point := (congrArg ((T).pairedComplex.vertexPoint (Fcut).retain) source).trans
      (K.vertexPoint_compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side)
    have zero := injective (initial.symm.trans point)
    exact (congrArg Subtype.val (edge_start 0)).trans (congrArg Subtype.val zero)
  have final_time : (time (Fin.last (n + 1))).val = τ := by
    have point := (congrArg ((T).pairedComplex.vertexPoint (Fcut).retain) finish).trans
      (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher
        M positive inner_disk beta acute W r side)
    have final := injective (terminal.symm.trans point)
    exact (congrArg Subtype.val (TriangleComplex.boundaryChainIntervalTime_last lower upper)).trans
      (congrArg Subtype.val final)
  refine ⟨time, increasing, zero_time, final_time, ?_⟩
  intro i u
  simpa only [edge_start, edge_finish] using exact_match i u

/-- Construct an entire terminal chain with its strictly increasing original ray times.
Every directed bank point and both original endpoint times are retained exactly. -/
theorem exists_compatibleMeshTerminalBank_parameterized_chain :
    ∃ n : ℕ, ∃ chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n,
      ∃ time : Fin (n + 2) → Set.Icc (0 : ℝ) τ, ∃ increasing : StrictMono time,
      (time 0).val = 0 ∧ (time (Fin.last (n + 1))).val = τ ∧
      ∀ (i : Fin (n + 1)) (u : unitInterval),
        (T).pairedComplex.directedBoundaryPath (chain.point i) u =
          K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W r side
            (closedNonnegativeIntervalLineMap (time i.castSucc).val (time i.succ).val τ
              (time i.castSucc).property.1
              (increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
              (time i.succ).property.2 u) := by
  obtain ⟨n, chain, index, named, _, source, finish⟩ :=
    K.exists_compatibleMeshTerminalBank_chain compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side
  have selected (i : Fin (n + 1)) : chain.point i ∈
      K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side := by
    rw [named]
    exact (index i).property
  obtain ⟨time, increasing, initial, terminal, matching⟩ :=
    K.parameterize_compatibleMeshTerminalBank_chain compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side chain selected source finish
  exact ⟨n, chain, time, increasing, initial, terminal, matching⟩

include W side in
/-- The actual whole spatial chain retains the original strictly increasing terminal-ray
parameters, including the source and truncation endpoint. Height coordinates are preserved. -/
theorem exists_compatibleMeshTerminalBank_spatial_chain :
    ∃ n : ℕ, ∃ chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n,
      ∃ time : Fin (n + 2) → Set.Icc (0 : ℝ) τ, StrictMono time ∧
      (time 0).val = 0 ∧ (time (Fin.last (n + 1))).val = τ ∧
      ∀ i, ((T).pairedFolding.boundarySpatialChain chain).vertex i =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) (time i).val) := by
  obtain ⟨n, chain, time, increasing, initial, terminal, matching⟩ :=
    K.exists_compatibleMeshTerminalBank_parameterized_chain compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side
  have points (i : Fin (n + 1)) (u : unitInterval) :
      ((T).pairedFolding.boundarySpatialChain chain).point i u =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r)
          (closedNonnegativeIntervalLineMap (time i.castSucc).val (time i.succ).val τ
            (time i.castSucc).property.1
            (increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
            (time i.succ).property.2 u).val) :=
    ((T).pairedFolding.boundarySpatialChain_point chain i u).trans
      ((congrArg ((T).pairedFolding.toSpace (Fcut).retain) (matching i u)).trans
        (K.fold_compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side _))
  refine ⟨n, chain, time, increasing, initial, terminal, fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have last := points (Fin.last n) 1
    rw [PolygonalChain.point_one, closedIntervalLineMap_one, Fin.succ_last] at last
    exact last
  · have first := points j 0
    rw [PolygonalChain.point_zero, closedIntervalLineMap_zero] at first
    exact first

end Unfoldings.ConvexRoof
