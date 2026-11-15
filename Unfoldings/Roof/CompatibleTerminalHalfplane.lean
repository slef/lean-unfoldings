module

public import Unfoldings.Roof.CompatibleWholeTerminalBanks
public import Unfoldings.Metric.PlacedBallComposition

/-! Exact original halfplane charts on the constructed full-forest whole terminal banks. -/

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

local instance terminalHalfplaneIndexFintype : Fintype W.Index := W.finiteIndex

/-- Every positive point of each constructed whole terminal bank has an exact whole
halfplane metric ball in its original support coordinates and spatial placement. -/
theorem exists_wholeTerminalBank_halfplane_chart (r : {v // v ∈ R.parents.roots})
    (side : Bool) (t : ℝ≥0) (positive : 0 < t.val) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val =
          (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ D : Metric.eball (K.wholeTerminalBank compact nonempty R no_boundary W r side t)
          (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (W.partition.restoreCut R.carrier y.val).val := by
  let B := W.terminalSupportCells r
  let Q := M.plane (W.partition.support (B.anchor side))
  let g := B.oneRayBankDilation side
  let x := K.wholeTerminalBank compact nonempty R no_boundary W r side t
  let F := W.partition.forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r)
  have image : F x = g t := K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r
    g (B.horizontal_restoreCut_oneRayBank side) (Dilation.lipschitzWith g) t
  have position : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
      R.exterior.ray (R.terminalIndex r) t.val :=
    (congrArg Cap.horizontal
      (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t)).trans
        (SpatialEnvelope.horizontal_point M.plane _)
  obtain ⟨ρ, ρpos, C, agrees_C⟩ := K.exists_terminalRayCut_ball_chart compact nonempty R
    no_boundary W r positive x position
  obtain ⟨σ, σpos, a, model_center, H, agrees_H⟩ := B.exists_oneRayBank_chart side t positive
  have model_place : Q.place a.val =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) :=
    (congrArg Q.place model_center).trans
      (SpatialEnvelope.point_eq_place M.plane (W.partition.support (B.anchor side))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
          (B.anchor side) B.threshold (B.tail side) t.val t.property)).symm
  let place : W.partition.faceSideHalfspace (B.anchor side)
      (orientMap (R.exterior.point (R.terminalIndex r))
        (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r) → Space :=
    fun z => Q.place z.val
  have place_injective : Function.Injective place :=
    fun z w equal => Subtype.ext (Q.place.injective equal)
  obtain ⟨ε, εpos, D, agrees⟩ := exists_composed_placed_ball_chart F
    (fun z => (W.partition.restoreCut R.carrier z).val)
    (fun z => (W.partition.restoreCut (R.terminalRayCut r) z).val)
    place place_injective image
    (fun z => congrArg PolygonalPoint.val (W.partition.restoreCut_forgetCut R.carrier
      (R.terminalRayCut r) (R.terminalRayCut_subset_carrier r) z))
    ρpos σpos C agrees_C H agrees_H
    (model_place.trans (B.restoreCut_oneRayBank side t).symm)
  exact ⟨ε, εpos, a, model_center, D, agrees⟩

end Unfoldings.ConvexRoof
