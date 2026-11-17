module

public import Unfoldings.Roof.CompatibleComparisonTerminalChainModel
public import Unfoldings.Polyhedron.BoundaryFanAngle
public import Unfoldings.Geometry.OppositeRayAngles
public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers

/-! Actual spatial endpoint angles and one-sided turn bounds of comparison terminal chains. -/

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

local instance comparisonTerminalChainTurnsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "HigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "VAt[" L "," h "]" => R.levelWindowModel M L HigherAt[L,h]
local notation "ProperAt[" L "," h "]" => R.levelWindow_proper M L HigherAt[L,h]
local notation "FullAt[" L "," h "]" => R.levelWindow_full M L HigherAt[L,h]
local notation "DomainAt[" L "]" => SpatialEnvelope.levelEquation_domain M.plane (-L)
local notation "Heights" => Set.eqOn_refl (SpatialEnvelope.height M.plane) _
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_cut_disjoint_interior compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S L h
local notation "ConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RemovedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.removed_edge_mem_cut
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RetainedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.retained_openSeamImage_disjoint
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S L h)

open Classical in
local instance comparisonTerminalChainTurnsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChainTurnsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {r : {v // v ∈ R.parents.roots}} {side : Bool}
  (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered r side)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}

open Classical in
/-- The two actual boundary directions at every internal terminal hinge are opposite,
so its complete intrinsic fan has angle at least pi. -/
theorem CompatibleComparisonTerminalChainModel.angle_ge_pi (i : Fin D.length) :
    Real.pi ≤ (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        (D.chain.point i.succ)) := by
  have bound := (NewAt[S,later,ordered]).pairedFolding.boundary_endpoint_angle_le_totalAngle
    (D.chain.point i.succ)
  have mate : (NewAt[S,later,ordered]).pairedComplex.boundaryMate NewRetainAt[S,later,ordered]
      (D.chain.point i.succ) =
    (NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
      (D.chain.point i.castSucc) := D.chain.mate_succ i
  rw [mate, (NewAt[S,later,ordered]).pairedFolding.germDirection_boundaryTurn,
    D.spatialVector i.succ, D.spatialVector i.castSucc, ← neg_smul] at bound
  rw [angle_smul_self_of_mul_neg
    (R.exterior.spatialDirection_ne_zero (R.terminalIndex r))
    (mul_neg_of_pos_of_neg (sub_pos.mpr (D.forward i.succ))
      (neg_neg_of_pos (sub_pos.mpr (D.forward i.castSucc))))] at bound
  exact bound

open Classical in
/-- Every actual one-sided turn of the terminal chain is weakly nonpositive. -/
theorem CompatibleComparisonTerminalChainModel.turn_nonpositive (i : Fin D.length) :
    Real.pi - (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        (D.chain.point i.succ)) ≤ 0 := sub_nonpos.mpr (D.angle_ge_pi i)

open Classical in
/-- Real intrinsic rolling headings of the actual terminal chain are weakly decreasing. -/
theorem CompatibleComparisonTerminalChainModel.heading_antitone :
    Antitone ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading D.chain) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  change Fin.partialSum _ i.succ ≤ Fin.partialSum _ i.castSucc
  rw [Fin.partialSum_succ]
  exact add_le_of_nonpos_right (D.turn_nonpositive i)

open Classical in
/-- An internal terminal-chain hinge is an interior original vertex of the larger roof. -/
theorem CompatibleComparisonTerminalChainModel.full_vertex_internal (i : Fin D.length) :
    ¬ (NewAt[S,later,ordered]).pairedComplex.IsBoundaryVertex Set.univ
      ((NewAt[S,later,ordered]).pairedComplex.vertexForgetCuts
        (Set.subset_univ NewRetainAt[S,later,ordered])
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          (D.chain.point i.succ))) := by
  let vertex := (NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex
    NewRetainAt[S,later,ordered] (D.chain.point i.succ)
  let new_inside := K.compatible_section_interior compact nonempty R later
    HigherAt[later,ordered] M
  let roof := (NewAt[S,later,ordered]).toTriangulation.roof ConformingAt[S,later,ordered] new_inside
  have position : roof.projectedVertex
      ((NewAt[S,later,ordered]).pairedComplex.vertexForgetCuts
        (Set.subset_univ NewRetainAt[S,later,ordered]) vertex) =
      R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + (D.lower i.succ).val) :=
    ((NewAt[S,later,ordered]).toTriangulation.roof_projectedVertex_vertexForgetCuts
      ConformingAt[S,later,ordered] new_inside NewRetainAt[S,later,ordered] vertex).trans
      ((congrArg (fun z => Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] z)) (D.vertexPoint i.succ)).trans
        ((congrArg Cap.horizontal
          (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
            level higher M positive inner_disk beta acute W S later ordered r side
              (D.lower i.succ))).trans (SpatialEnvelope.horizontal_point _ _)))
  apply (roof.projectedVertex_mem_interior_iff _).mp
  rw [(NewAt[S,later,ordered]).toTriangulation.roof_footprint, M.clip_eq_sublevel, neg_neg,
    position]
  apply (K.clippedExtension slopes compact nonempty).mem_interior_sublevel
  apply (R.terminal_ray_below_iff later HigherAt[later,ordered] r
    (add_nonneg (R.terminalTime_pos level higher r).le (D.lower i.succ).property.1)).mpr
  linarith [(D.internal i).2]

open Classical in
/-- Every actual terminal-chain hinge is exactly straight. Restoring its cuts embeds the
complete fan in the original convex vertex link; zero spatial bend forces zero intrinsic turn. -/
theorem CompatibleComparisonTerminalChainModel.angle_eq_pi (i : Fin D.length) :
    (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        (D.chain.point i.succ)) = Real.pi := by
  let roof := (NewAt[S,later,ordered]).toTriangulation.roof ConformingAt[S,later,ordered]
    (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M)
  have internal := D.full_vertex_internal i
  have bound := (NewAt[S,later,ordered]).pairedFolding.abs_boundary_turn_le_spatial_bend
    (D.chain.point i.succ) internal (roof.totalAngle_le_two_pi _ internal)
  have mate : (NewAt[S,later,ordered]).pairedComplex.boundaryMate NewRetainAt[S,later,ordered]
      (D.chain.point i.succ) =
    (NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
      (D.chain.point i.castSucc) := D.chain.mate_succ i
  rw [mate, (NewAt[S,later,ordered]).pairedFolding.germDirection_boundaryTurn,
    D.spatialVector i.succ, D.spatialVector i.castSucc,
    InnerProductGeometry.angle_neg_neg,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (sub_pos.mpr (D.forward i.succ)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (sub_pos.mpr (D.forward i.castSucc)),
    InnerProductGeometry.angle_self (R.exterior.spatialDirection_ne_zero (R.terminalIndex r))]
    at bound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp bound) |>.symm

open Classical in
/-- Every unreduced real heading of the actual terminal-chain roll is exactly zero. -/
theorem CompatibleComparisonTerminalChainModel.heading_eq_zero (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading D.chain i = 0 :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading_eq_zero D.chain D.angle_eq_pi i

open Classical in
/-- Every edge of the actual canonical roll is its positive original length on the real axis. -/
theorem CompatibleComparisonTerminalChainModel.rolledEdge (i : Fin (D.length + 1)) :
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).edge i =
      ((((D.upper i).val - (D.lower i).val) *
        ‖R.exterior.spatialDirection (R.terminalIndex r)‖ : ℝ) : ℂ) := by
  rw [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge, D.heading_eq_zero,
    D.bankLength]
  simp [polarRay]

end Unfoldings.ConvexRoof
