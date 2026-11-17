module

public import Unfoldings.Roof.CompatibleProcessedTerminalBanks
public import Unfoldings.Roof.CompatibleTerminalHalfplane
public import Unfoldings.Geometry.SpatialEnvelopeCutBall
public import Unfoldings.Roof.RestoredTerminalHalfplane

/-! Original terminal halfplane charts survive every processing stage beyond the finite window. -/

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

local instance processedTerminalChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance processedTerminalChartWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Restoring unprocessed cuts preserves a whole original intrinsic ball at every
terminal bank point beyond the finite window. The actual canonical map is retained. -/
theorem exists_compatibleMeshProcessed_terminal_restore_chart
    (S : (Fcut).parents.ParentFrontier) (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) (after : R.terminalTime level r < t.val) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B :
      Metric.eball (K.wholeTerminalBank compact nonempty R no_boundary W r side t)
        (ENNReal.ofReal ε) ≃ᵢ
      Metric.eball
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
          r side t) (ENNReal.ofReal ε),
      ∀ y, (B y).val = W.partition.forgetCut R.carrier CutsAt[S] IncludedAt[S] y.val := by
  have above : level < (K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex r) t.val) := by
    apply lt_of_not_ge
    intro below
    exact (not_lt_of_ge ((R.terminal_ray_sublevel_iff level higher r t.property).mp below)) after
  obtain ⟨δ, radius_positive, germ⟩ := K.exists_compatibleMeshProcessed_cut_germ_outside compact
    nonempty R no_boundary level higher M positive inner_disk beta acute S above
  apply W.partition.exists_forgetCut_ball_chart_at R.carrier CutsAt[S] IncludedAt[S]
    (K.wholeTerminalBank compact nonempty R no_boundary W r side t) radius_positive
  intro z near
  apply germ z
  have point := (congrArg Cap.horizontal
    (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t)).trans
      (SpatialEnvelope.horizontal_point _ _)
  rwa [point] at near

/-- Every original outer bank has a whole halfplane metric chart at every processing stage,
with its original rigid supporting frame and literal spatial placement unchanged. -/
theorem exists_compatibleMeshProcessed_terminal_halfplane_chart
    (S : (Fcut).parents.ParentFrontier) (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) (after : R.terminalTime level r < t.val) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val =
          (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball
          (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
            r side t) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (W.partition.restoreCut CutsAt[S] y.val).val := by
  have above : level < (K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex r) t.val) := by
    apply lt_of_not_ge
    intro below
    exact (not_lt_of_ge ((R.terminal_ray_sublevel_iff level higher r t.property).mp below)) after
  obtain ⟨δ, radius_positive, germ⟩ := K.exists_compatibleMeshProcessed_cut_germ_outside compact
    nonempty R no_boundary level higher M positive inner_disk beta acute S above
  exact K.exists_restoredWholeTerminalBank_halfplane_chart compact nonempty R no_boundary W
    CutsAt[S] IncludedAt[S] r side t ((R.terminalTime_pos level higher r).trans after)
    radius_positive germ

end Unfoldings.ConvexRoof
