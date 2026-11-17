module

public import Unfoldings.Roof.RestoredWholeTerminalBanks
public import Unfoldings.Roof.CompatibleTerminalHalfplane
public import Unfoldings.Geometry.SpatialEnvelopeCutBall
public import Unfoldings.Metric.RestoredPlacedBall

/-! Exact original terminal halfplane charts survive any locally unchanged partial cut. -/

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
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance restoredTerminalChartIndexFintype : Fintype W.Index := W.finiteIndex

variable (cuts : Set Plane) (included : cuts ⊆ R.carrier)

/-- Every original terminal bank has a whole halfplane chart when the cut germ is unchanged,
with its original rigid supporting frame and literal spatial placement unchanged. -/
theorem exists_restoredWholeTerminalBank_halfplane_chart
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0) (positive : 0 < t.val)
    {δ : ℝ} (radius_positive : 0 < δ)
    (germ : ∀ z, dist z (R.exterior.ray (R.terminalIndex r) t.val) < δ →
      (z ∈ R.carrier ↔ z ∈ cuts)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val =
          (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball
          (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included
            r side t) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (W.partition.restoreCut cuts y.val).val := by
  obtain ⟨ρ, ρpos, C, agrees_C⟩ := W.partition.exists_forgetCut_ball_chart_at R.carrier cuts
    included (K.wholeTerminalBank compact nonempty R no_boundary W r side t) radius_positive (by
      intro z near
      apply germ z
      have point := (congrArg Cap.horizontal
        (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t)).trans
          (SpatialEnvelope.horizontal_point _ _)
      rwa [point] at near)
  obtain ⟨σ, σpos, a, center, H, agrees_H⟩ := K.exists_wholeTerminalBank_halfplane_chart compact
    nonempty R no_boundary W r side t positive
  let plane := M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))
  have model_place : plane.place a.val =
      (W.partition.restoreCut R.carrier
        (K.wholeTerminalBank compact nonempty R no_boundary W r side t)).val := by
    have physical := SpatialEnvelope.point_eq_place M.plane
      (W.partition.support ((W.terminalSupportCells r).anchor side))
      (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
        ((W.terminalSupportCells r).anchor side) (W.terminalSupportCells r).threshold
        ((W.terminalSupportCells r).tail side) t.val t.property)
    exact (congrArg plane.place center).trans (physical.symm.trans
      (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t).symm)
  obtain ⟨ε, εpos, D, agrees⟩ := exists_restored_placed_ball_chart
    (W.partition.forgetCut R.carrier cuts included)
    (fun z => (W.partition.restoreCut R.carrier z).val)
    (fun z => (W.partition.restoreCut cuts z).val)
    (fun z => plane.place z.val) (fun z w eq => Subtype.ext (plane.place.injective eq))
    (fun z => congrArg PolygonalPoint.val
      (W.partition.restoreCut_forgetCut R.carrier cuts included z))
    ρpos σpos C agrees_C H agrees_H model_place
  exact ⟨ε, εpos, a, center, D, agrees⟩

end Unfoldings.ConvexRoof
