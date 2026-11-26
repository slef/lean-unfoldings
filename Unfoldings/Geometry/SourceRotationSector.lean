module

public import Unfoldings.Geometry.OrientedBankGapSourceChart
public import Unfoldings.Geometry.SourceOpeningBankGap
public import Unfoldings.Cone.ComplementarySectorRadial
public import Unfoldings.Metric.CenteredBallChartRestriction

/-! The tip of a rotated bank gap has the sector of the rotation angle. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.OrientedBankGap

/-- A rotation of the whole original bank gives a sector chart at the tip with
its two literal initial edge parameters along the two angular boundaries. -/
theorem sourceRotation_angular_chart {n : ℕ} (first : PolygonalRay ℂ (n + 1))
    {κ : ℝ} (positive : 0 < κ) (small : κ < 2 * Real.pi)
    (genuine : first.chain.edge 0 ≠ 0)
    (G : OrientedBankGap first (first.rotateSuffix 0 κ)) :
    let d := first.chain.edge 0
    let x := G.model.edgePoint false 0 0
    0 < ‖d‖ ∧ ∃ chart : Metric.eball x (ENNReal.ofReal ‖d‖) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin positive.le) (ENNReal.ofReal ‖d‖),
      ∀ (side : Bool) (t : unitInterval)
        (near : edist (G.model.edgePoint side 0 t) x < ENNReal.ofReal ‖d‖),
        (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val =
          if side then (t.val * ‖d‖) • polarRay κ else (t.val * ‖d‖ : ℝ) := by
  let second := first.rotateSuffix 0 κ
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  have same_start : second.start = first.start := first.rotateSuffix_start 0 κ
  have rotated : e = complexRotation κ d := first.rotateSuffix_zero_edge κ 0
  have length : ‖e‖ = ‖d‖ := (congrArg norm rotated).trans ((complexRotation κ).norm_map d)
  have radius : min ‖d‖ ‖e‖ = ‖d‖ := min_eq_left length.ge
  have d_ne : d ≠ 0 := genuine
  have e_ne : e ≠ 0 := rotated.symm ▸ by
    simpa only [map_zero] using (complexRotation κ).injective.ne d_ne
  have result := G.exists_model_source_chart d_ne e_ne
  change 0 < min ‖d‖ ‖e‖ ∧ _ ∧ _ at result
  rw [radius] at result
  obtain ⟨rpos, bounds, chart, physical⟩ := result
  change initialGapAngle d e ∈ Set.Ioo (0 : ℝ) Real.pi at bounds
  have exact_angle := initialGapAngle_rotated_of_bounds d d_ne positive small (rotated ▸ bounds)
  have angle := (congrArg (initialGapAngle d) rotated).trans exact_angle.1
  let X := planarSector (initialGapAngle d e)
  have convex : Convex ℝ X := convex_planarSector _
  let E : X ≃ᵢ PolygonalPoint X :=
    ⟨⟨PolygonalPoint.includeConvex X (Set.Subset.refl X),
      fun z => ⟨z.val, z.property⟩, fun _ => rfl, fun _ => rfl⟩,
      PolygonalPoint.includeConvex_isometry X convex (Set.Subset.refl X)⟩
  let B := E.trans (PolygonalPoint.congrIsometryEquiv
    (show X = closedAngularSector κ by
      change planarSector (initialGapAngle d e) = _
      rw [angle]
      exact planarSector_eq_closedAngularSector positive exact_angle.2))
  have center : B (initialGapSectorOrigin d e) =
      closedAngularSectorOrigin (positive.le) := by
    apply PolygonalPoint.ext
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val]
    rfl
  let balls := basedEBallIsometry B (initialGapSectorOrigin d e) _ center (ENNReal.ofReal ‖d‖)
  let charts := chart.trans ((metricBallEBallEquiv (initialGapSectorOrigin d e) ‖d‖).trans balls)
  refine ⟨rpos, charts, ?_⟩
  intro side t near
  have image := G.source_chart_bank_coordinates same_start d_ne e_ne chart physical side t near
  change (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val = _ at image
  change (B (chart ⟨G.model.edgePoint side 0 t, near⟩).val).val = _
  rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val]
  change (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val = _
  rw [image, angle, length]

end Unfoldings.OrientedBankGap
