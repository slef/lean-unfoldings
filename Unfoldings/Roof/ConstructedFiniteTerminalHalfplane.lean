module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankMetric
public import Unfoldings.Roof.CompatibleMeshCornerCharts
public import Unfoldings.Roof.CompatibleTerminalHalfplane
public import Unfoldings.Cone.PlacedTangentCharts

/-! Whole original halfplane neighborhoods of every interior finite terminal-bank copy. -/

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

local instance finiteTerminalHalfplaneIndexFintype : Fintype (T).Index :=
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

local instance finiteTerminalHalfplaneWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- Every positive finite terminal-bank point strictly below truncation has its original
whole halfplane metric neighborhood, with exact support coordinates and spatial folding.
This applies at original subdivision vertices as well as open fine-edge points. -/
theorem exists_compatibleMeshTerminalBank_halfplane_chart (t : Set.Icc (0 : ℝ) τ)
    (tpos : 0 < t.val) (before : t.val < τ) :
    ∃ (ε : ℝ) (εpos : 0 < ε),
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val =
          (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
            (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball
          (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W r side t) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          (D ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr εpos)⟩).val = a ∧
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (T).pairedFolding.toSpace (Fcut).retain y.val := by
  let source := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side t
  let target := K.wholeTerminalBank compact nonempty R no_boundary W r side
    ⟨t.val, t.property.1⟩
  let Qsupport := M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))
  let inclusion := K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W
  have image : inclusion source = target := K.compatibleMeshWholeMap_terminalBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side t
  have position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain source) =
      R.exterior.ray (R.terminalIndex r) t.val :=
    (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side t)).trans
      (SpatialEnvelope.horizontal_point M.plane _)
  have below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain source)) < level :=
    (congrArg (K.clippedExtension slopes compact nonempty).height position).trans_lt
      ((R.terminal_ray_below_iff level higher r t.property.1).mpr before)
  obtain ⟨ρ, ρpos, chart, agrees_chart⟩ := K.compatibleMesh_ball_chart_at compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W source below
  obtain ⟨σ, σpos, a, coordinates, H, agrees_H⟩ :=
    K.exists_wholeTerminalBank_halfplane_chart compact nonempty R no_boundary W r side
      ⟨t.val, t.property.1⟩ tpos
  let place : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
      (orientMap (R.exterior.point (R.terminalIndex r))
        (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r) → Space :=
    fun z => Qsupport.place z.val
  have place_injective : Function.Injective place :=
    fun z w equal => Subtype.ext (Qsupport.place.injective equal)
  have model_place : place a = (W.partition.restoreCut R.carrier target).val := by
    exact ((congrArg Qsupport.place coordinates).trans
      (SpatialEnvelope.point_eq_place M.plane
        (W.partition.support ((W.terminalSupportCells r).anchor side))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
          ((W.terminalSupportCells r).anchor side) (W.terminalSupportCells r).threshold
          ((W.terminalSupportCells r).tail side) t.val t.property.1)).symm).trans
      (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side
        ⟨t.val, t.property.1⟩).symm
  obtain ⟨ε, εpos, D, agrees⟩ := exists_composed_placed_ball_chart inclusion
    ((T).pairedFolding.toSpace (Fcut).retain)
    (fun z => (W.partition.restoreCut R.carrier z).val) place place_injective image
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W) ρpos σpos chart agrees_chart H agrees_H model_place
  have place_source : place a = (T).pairedFolding.toSpace (Fcut).retain source :=
    model_place.trans
      ((congrArg (fun z => (W.partition.restoreCut R.carrier z).val) image).symm.trans
      (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W source))
  have center : (D ⟨source, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr εpos)⟩).val = a :=
    place_injective ((agrees _).trans place_source.symm)
  exact ⟨ε, εpos, a, coordinates, D, center, agrees⟩

/-- A specified original finite corner on a positive terminal bank has its actual retained
fan modeled by the original halfplane. Every original tangent-cell placement is preserved. -/
theorem exists_compatibleMeshTerminal_vertex_halfplane_chart (t : Set.Icc (0 : ℝ) τ)
    (tpos : 0 < t.val) (before : t.val < τ)
    (vertex : (T).pairedComplex.Vertex (Fcut).retain)
    (position : (T).pairedComplex.vertexPoint (Fcut).retain vertex =
      K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
        beta acute W r side t) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val =
          (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
            (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball ((T).pairedComplex.tangentOrigin (Fcut).retain vertex)
          (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ (b : (T).pairedComplex.TangentTotal (Fcut).retain vertex)
            (near : edist ((T).pairedComplex.tangentPoint (Fcut).retain vertex b)
              ((T).pairedComplex.tangentOrigin (Fcut).retain vertex) < ENNReal.ofReal ε),
            (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
              (D ⟨(T).pairedComplex.tangentPoint (Fcut).retain vertex b, near⟩).val.val =
                (T).pairedFolding.toSpace (Fcut).retain
                  ((T).pairedComplex.tangentSurfaceTag (Fcut).retain vertex b) := by
  obtain ⟨ρ, ρpos, a, coordinates, H, center_H, agrees_H⟩ :=
    K.exists_compatibleMeshTerminalBank_halfplane_chart compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side t tpos before
  let source := (T).pairedComplex.vertexPoint (Fcut).retain vertex
  let target := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side t
  let move := basedEBallIsometry (IsometryEquiv.refl _) source target position (ENNReal.ofReal ρ)
  let chart := move.trans H
  have center : (chart ⟨source, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩).val = a := by
    have moved : move ⟨source, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩ =
        ⟨target, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩ := Subtype.ext position
    change (H (move _)).val = a
    rw [moved]
    exact center_H
  obtain ⟨ε, εpos, D, agrees⟩ := (T).pairedFolding.exists_placed_tangentChart (Fcut).retain vertex
    (fun z => (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place z.val)
    ρpos chart center (fun z => agrees_H (move z))
  exact ⟨ε, εpos, a, coordinates, D, agrees⟩

end Unfoldings.ConvexRoof
