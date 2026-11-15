module

public import Unfoldings.Roof.CompatibleTerminalHalfplane

/-! Whole-bank halfplane charts retain the exact original bank ray coordinates. -/

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

local instance terminalChartCoordinateIndexFintype : Fintype W.Index := W.finiteIndex

/-- Whole halfplane charts retain both spatial placement and every nearby actual bank
point's original rigid ray coordinate, on the same full-forest metric copies. -/
theorem exists_wholeTerminalBank_chart_with_bank_coordinates (r : {v // v ∈ R.parents.roots})
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
          (∀ y, (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
            (D y).val.val = (W.partition.restoreCut R.carrier y.val).val) ∧
          ∀ (s : ℝ≥0) (near : edist
            (K.wholeTerminalBank compact nonempty R no_boundary W r side s)
            (K.wholeTerminalBank compact nonempty R no_boundary W r side t) < ENNReal.ofReal ε),
            (D ⟨K.wholeTerminalBank compact nonempty R no_boundary W r side s, near⟩).val.val =
              (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).project.symm
                (R.exterior.ray (R.terminalIndex r) s.val) := by
  obtain ⟨ε, εpos, a, center, D, placement⟩ := K.exists_wholeTerminalBank_halfplane_chart compact
    nonempty R no_boundary W r side t positive
  refine ⟨ε, εpos, a, center, D, placement, ?_⟩
  intro s near
  let B := W.terminalSupportCells r
  let Q := M.plane (W.partition.support (B.anchor side))
  apply Q.place.injective
  exact (placement _).trans
    ((K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side s).trans
      (SpatialEnvelope.point_eq_place M.plane (W.partition.support (B.anchor side))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
          (B.anchor side) B.threshold (B.tail side) s.val s.property)))

end Unfoldings.ConvexRoof
