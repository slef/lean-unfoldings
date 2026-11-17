module

public import Unfoldings.Roof.CompatibleProcessedTerminalCharts
public import Unfoldings.Roof.CompatibleComparisonPlacedCharts
public import Unfoldings.Roof.TerminalRayLevelInterval
public import Unfoldings.Cone.PlacedTangentCenterTransport

/-! Original terminal halfplanes and fans in actual larger comparison meshes. -/

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

local instance comparisonTerminalChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "BankAt[" S "," r "," side "," t "]" =>
  K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side t

open Classical in
local instance comparisonTerminalNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

/-- Every original terminal point strictly below the new level has its exact original height. -/
theorem compatibleMeshProcessed_terminal_below_comparison
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0)
    (before : t.val < R.terminalTime later r) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] BankAt[S,r,side,t]).val) < later := by
  rw [K.restore_restoredWholeTerminalBank, SpatialEnvelope.horizontal_point]
  exact (R.terminal_ray_below_iff later (fun v => (higher v).trans ordered) r t.property).mpr before

open Classical in
/-- The actual original terminal-bank copy in the constructed larger comparison mesh. -/
@[macro_inline] def compatibleMeshProcessedComparisonTerminalBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0)
    (before : t.val < R.terminalTime later r) :
    (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S later ordered BankAt[S,r,side,t]
    (K.compatibleMeshProcessed_terminal_below_comparison compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side t before)

local notation "TerminalAt[" S "," L "," h "," r "," side "," t "," ht "]" =>
  K.compatibleMeshProcessedComparisonTerminalBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h r side t ht

open Classical in
/-- The terminal comparison lift keeps the literal original whole-cut bank copy. -/
theorem compatibleMeshProcessedComparisonWholeMap_terminalBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0)
    (before : t.val < R.terminalTime later r) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered TerminalAt[S,later,ordered,r,side,t,before] =
        BankAt[S,r,side,t] :=
  K.compatibleMeshProcessedComparisonWholeMap_lift compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered BankAt[S,r,side,t] _

open Classical in
/-- Each positive outer comparison-bank point has its whole original halfplane, preserving
the supporting frame, original ray parameter, center and full spatial placement. -/
theorem exists_compatibleMeshProcessedComparisonTerminal_halfplane_chart
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0)
    (after : R.terminalTime level r < t.val) (before : t.val < R.terminalTime later r) :
    ∃ radius : ℝ, ∃ radius_positive : 0 < radius,
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball TerminalAt[S,later,ordered,r,side,t,before] (ENNReal.ofReal radius) ≃ᵢ
            Metric.ball a radius,
          (D ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_positive)⟩).val = a ∧
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (NewAt[S,later,ordered]).pairedFolding.toSpace
              NewRetainAt[S,later,ordered] y.val := by
  obtain ⟨σ, σpos, a, coordinates, H, agrees_H⟩ :=
    K.exists_compatibleMeshProcessed_terminal_halfplane_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S r side t after
  let support := M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))
  let place : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
      (orientMap (R.exterior.point (R.terminalIndex r))
        (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r) → Space :=
    fun z => support.place z.val
  have injective : Function.Injective place := fun z w same =>
    Subtype.ext (support.place.injective same)
  have model_place : place a = (W.partition.restoreCut CutsAt[S] BankAt[S,r,side,t]).val := by
    exact ((congrArg support.place coordinates).trans
      (SpatialEnvelope.point_eq_place M.plane (W.partition.support
        ((W.terminalSupportCells r).anchor side))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
          ((W.terminalSupportCells r).anchor side) (W.terminalSupportCells r).threshold
          ((W.terminalSupportCells r).tail side) t.val t.property)).symm).trans
      (K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
        r side t).symm
  obtain ⟨radius, positive_radius, D, center, agrees⟩ :=
    K.exists_compatibleMeshProcessedComparison_placed_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered BankAt[S,r,side,t]
      (K.compatibleMeshProcessed_terminal_below_comparison compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered r side t before)
      place injective a model_place ⟨σ, σpos, H, agrees_H⟩
  exact ⟨radius, positive_radius, a, coordinates, D, center, agrees⟩

open Classical in
/-- Every actual fine vertex on a positive outer comparison bank has its full original
halfplane fan. The point-copy equality specifies the vertex, not a fan-matching hypothesis. -/
theorem exists_compatibleMeshProcessedComparisonTerminal_vertex_halfplane_chart
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0)
    (after : R.terminalTime level r < t.val) (before : t.val < R.terminalTime later r)
    (vertex : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered])
    (position : (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      vertex = TerminalAt[S,later,ordered,r,side,t,before]) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball ((NewAt[S,later,ordered]).pairedComplex.tangentOrigin
              NewRetainAt[S,later,ordered] vertex) (ENNReal.ofReal radius) ≃ᵢ Metric.ball a radius,
          ∀ (b : (NewAt[S,later,ordered]).pairedComplex.TangentTotal
              NewRetainAt[S,later,ordered] vertex)
            (near : edist ((NewAt[S,later,ordered]).pairedComplex.tangentPoint
                NewRetainAt[S,later,ordered] vertex b)
              ((NewAt[S,later,ordered]).pairedComplex.tangentOrigin
                NewRetainAt[S,later,ordered] vertex) < ENNReal.ofReal radius),
            (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
              (D ⟨(NewAt[S,later,ordered]).pairedComplex.tangentPoint
                NewRetainAt[S,later,ordered] vertex b, near⟩).val.val =
                (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
                  ((NewAt[S,later,ordered]).pairedComplex.tangentSurfaceTag
                    NewRetainAt[S,later,ordered] vertex b) := by
  obtain ⟨ρ, ρpos, a, coordinates, H, center_H, agrees_H⟩ :=
    K.exists_compatibleMeshProcessedComparisonTerminal_halfplane_chart compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side t after before
  obtain ⟨radius, positive_radius, D, agrees⟩ :=
    (NewAt[S,later,ordered]).pairedFolding.exists_placed_tangentChart_of_point_eq
      NewRetainAt[S,later,ordered] vertex
      (fun z => (M.plane (W.partition.support
        ((W.terminalSupportCells r).anchor side))).place z.val)
      position ρpos H center_H agrees_H
  exact ⟨radius, positive_radius, a, coordinates, D, agrees⟩

end Unfoldings.ConvexRoof
