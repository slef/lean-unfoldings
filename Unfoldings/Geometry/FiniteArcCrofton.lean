module

public import Unfoldings.Geometry.EquatorPhase
public import Unfoldings.Geometry.MinorArcCrofton

/-! Crofton for two finite spherical arcs via the uniform phase of the rotating arc. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open MeasureTheory InnerProductGeometry
open scoped ENNReal

/-- The equatorial arc of angular length (2r), centered on phase zero. -/
def equatorialArc (r : ℝ) : Set Space :=
  equatorPoint '' Metric.closedBall (0 : EquatorPhase) r

private def crossingRots (u v : Space) : Set SpatialRotation :=
  (fun g => linear g equatorPole) ⁻¹' spatialSignChange u v

private theorem crossingRots_measurable (u v : Space) : MeasurableSet (crossingRots u v) :=
  (spatialSignChange_measurable u v).preimage
    (continuous_apply.comp (continuous_id.prodMk continuous_const)).measurable

private def crossingPhase (u v : Space) (g : SpatialRotation) : EquatorPhase :=
  phaseAt (linear g⁻¹ (minorArcCrossingPoint (linear g equatorPole) u v))

private theorem crossingPhase_measurable (u v : Space) : Measurable (crossingPhase u v) := by
  have pole : Measurable (fun g : SpatialRotation => linear g equatorPole) :=
    (continuous_apply.comp (continuous_id.prodMk continuous_const)).measurable
  have point : Measurable (fun g : SpatialRotation => minorArcCrossingPoint
      (linear g equatorPole) u v) := (minorArcCrossingPoint_measurable u v).comp pole
  have inverse : Measurable (fun g : SpatialRotation => g⁻¹) := continuous_inv.measurable
  have pair : Measurable (fun g : SpatialRotation =>
      (g⁻¹, minorArcCrossingPoint (linear g equatorPole) u v)) := inverse.prodMk point
  have evaluate : Measurable (fun z : SpatialRotation × Space => linear z.1 z.2) :=
    continuous_apply.measurable
  have combined := measurable_phaseAt.comp (evaluate.comp pair)
  unfold crossingPhase
  exact combined

private theorem crossingPhase_equatorPoint {u v : Space} {g : SpatialRotation}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (crossing : g ∈ crossingRots u v) :
    equatorPoint (crossingPhase u v g) =
      linear g⁻¹ (minorArcCrossingPoint (linear g equatorPole) u v) := by
  let p := minorArcCrossingPoint (linear g equatorPole) u v
  obtain ⟨_, orthogonal, unit⟩ := minorArcCrossingPoint_spec hu hv not_antipodal crossing
  apply equatorPoint_phaseAt
  · change ‖isometry g⁻¹ p‖ = 1
    rwa [(isometry g⁻¹).norm_map]
  · change (linear g⁻¹ p) 2 = 0
    rw [← inner_equatorPole, ← inner_linear g, linear_apply_inv]
    exact orthogonal

private theorem crossingPhase_mul_phaseRotation {u v : Space} {g : SpatialRotation}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (crossing : g ∈ crossingRots u v) (t : EquatorPhase) :
    crossingPhase u v (g * phaseRotation t) = crossingPhase u v g - t := by
  have inv_shift :
      linear (phaseRotation t)⁻¹ (equatorPoint (crossingPhase u v g)) =
        equatorPoint (crossingPhase u v g - t) := by
    have h := linear_phaseRotation_equatorPoint t (crossingPhase u v g - t)
    rw [show t + (crossingPhase u v g - t) = crossingPhase u v g by abel] at h
    rw [← h, linear_inv_apply]
  unfold crossingPhase
  rw [mul_inv_rev, linear_mul, LinearMap.comp_apply, linear_mul, LinearMap.comp_apply,
    linear_phaseRotation_pole, ← crossingPhase_equatorPoint hu hv not_antipodal crossing,
    inv_shift]
  simp only [phaseAt_equatorPoint]

private theorem crossingRots_mul_phaseRotation {u v : Space} {g : SpatialRotation}
    (t : EquatorPhase) : g * phaseRotation t ∈ crossingRots u v ↔ g ∈ crossingRots u v := by
  simp only [crossingRots, Set.mem_preimage, linear_mul, LinearMap.comp_apply,
    linear_phaseRotation_pole]

private def arcCrossing (u v : Space) (r : ℝ) (g : SpatialRotation) : ℝ≥0∞ :=
  (crossingRots u v).indicator
    (fun h => (Metric.closedBall (0 : EquatorPhase) r).indicator (fun _ => 1) (crossingPhase u v h))
    g

private theorem arcCrossing_measurable (u v : Space) (r : ℝ) : Measurable (arcCrossing u v r) := by
  have arc : Measurable ((Metric.closedBall (0 : EquatorPhase) r).indicator
      (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator measurableSet_closedBall
  exact (arc.comp (crossingPhase_measurable u v)).indicator (crossingRots_measurable u v)

private theorem lintegral_arcCrossing {u v : Space} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (nonnegative : 0 ≤ r) (small : r ≤ Real.pi) :
    (∫⁻ g, arcCrossing u v r g ∂probability) =
      ENNReal.ofReal (angle u v * (2 * r) / (2 * Real.pi ^ 2)) := by
  have phase_average (g : SpatialRotation) :
      (∫⁻ t, arcCrossing u v r (g * phaseRotation t) ∂phaseProbability) =
        (crossingRots u v).indicator (fun _ => ENNReal.ofReal (r / Real.pi)) g := by
    by_cases cross : g ∈ crossingRots u v
    · let θ := crossingPhase u v g
      have shifted (t : EquatorPhase) :
          arcCrossing u v r (g * phaseRotation t) =
            (Metric.closedBall θ r).indicator (fun _ => 1) t := by
        have belongs : θ - t ∈ Metric.closedBall (0 : EquatorPhase) r ↔
            t ∈ Metric.closedBall θ r := by
          rw [Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right, dist_eq_norm,
            norm_sub_rev θ t]
        simp only [arcCrossing, Set.indicator_of_mem ((crossingRots_mul_phaseRotation t).2 cross),
          crossingPhase_mul_phaseRotation hu hv not_antipodal cross t]
        change (Metric.closedBall (0 : EquatorPhase) r).indicator (fun _ => (1 : ℝ≥0∞))
          (θ - t) = _
        by_cases h : t ∈ Metric.closedBall θ r
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (belongs.mpr h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (belongs.mp h'))]
      simp only [shifted, lintegral_indicator measurableSet_closedBall, lintegral_const,
        Measure.restrict_apply_univ, one_mul, Set.indicator_of_mem cross, phaseProbability_closedBall
          _ nonnegative small]
    · have outside (t : EquatorPhase) : g * phaseRotation t ∉ crossingRots u v :=
        fun inside => cross ((crossingRots_mul_phaseRotation t).1 inside)
      simp only [arcCrossing, Set.indicator_of_notMem (outside _), Set.indicator_of_notMem cross,
        lintegral_zero]
  have averaging := lintegral_eq_average_shifts phaseProbability (fun _ => 1) phaseRotation
    measurable_const continuous_phaseRotation.measurable (arcCrossing u v r)
    (arcCrossing_measurable u v r)
  simp only [one_mul, phase_average] at averaging
  have u_ne : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  have v_ne : v ≠ 0 := norm_ne_zero_iff.mp (by simp [hv])
  rw [← averaging, lintegral_indicator (crossingRots_measurable u v), lintegral_const,
    Measure.restrict_apply_univ, crossingRots,
    probability_spatialSignChange equatorPole_unit u_ne v_ne,
    ← ENNReal.ofReal_mul (div_nonneg nonnegative Real.pi_pos.le)]
  congr 1
  ring

private theorem rotated_equatorialArc_on_greatCircle {g : SpatialRotation} {r : ℝ} {x : Space}
    (arc : x ∈ linear g '' equatorialArc r) : inner ℝ (linear g equatorPole) x = 0 := by
  obtain ⟨_, ⟨t, _, rfl⟩, rfl⟩ := arc
  rw [inner_linear, inner_equatorPole, equatorPoint_vertical]

private theorem minorArc_equatorialArc_crossing_iff {u v : Space} {r : ℝ} {g : SpatialRotation}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (first : inner ℝ (linear g equatorPole) u ≠ 0)
    (last : inner ℝ (linear g equatorPole) v ≠ 0) :
    (∃! x ∈ openMinorArc u v, x ∈ linear g '' equatorialArc r) ↔
      g ∈ crossingRots u v ∧ crossingPhase u v g ∈ Metric.closedBall (0 : EquatorPhase) r := by
  constructor
  · rintro ⟨x, ⟨arc, rotated⟩, _⟩
    have on_plane := rotated_equatorialArc_on_greatCircle rotated
    have cross : g ∈ crossingRots u v :=
      spatialSignChange_of_minorArc_on_greatCircle hu hv not_antipodal first last arc on_plane
    refine ⟨cross, ?_⟩
    have unique := (minorArc_greatCircle_crossing_iff hu hv not_antipodal first last).mpr cross
    let p := minorArcCrossingPoint (linear g equatorPole) u v
    obtain ⟨hit, orthogonal, _⟩ := minorArcCrossingPoint_spec hu hv not_antipodal cross
    have equal : x = p := unique.unique ⟨arc, on_plane⟩ ⟨hit, orthogonal⟩
    obtain ⟨_, ⟨t, ht, rfl⟩, image⟩ := rotated
    rw [equal] at image
    have inverse := congrArg (linear g⁻¹) image
    rw [linear_inv_apply] at inverse
    have phase_eq : crossingPhase u v g = t :=
      equatorPoint_injective ((crossingPhase_equatorPoint hu hv not_antipodal cross).trans
        inverse.symm)
    rwa [phase_eq]
  · rintro ⟨cross, phase⟩
    let p := minorArcCrossingPoint (linear g equatorPole) u v
    obtain ⟨hit, orthogonal, _⟩ := minorArcCrossingPoint_spec hu hv not_antipodal cross
    have rotated : p ∈ linear g '' equatorialArc r :=
      ⟨equatorPoint (crossingPhase u v g), ⟨crossingPhase u v g, phase, rfl⟩, by
        rw [crossingPhase_equatorPoint hu hv not_antipodal cross, linear_apply_inv]⟩
    refine ⟨p, ⟨hit, rotated⟩, ?_⟩
    rintro x ⟨arc, other⟩
    have unique := (minorArc_greatCircle_crossing_iff hu hv not_antipodal first last).mpr cross
    exact unique.unique ⟨arc, rotated_equatorialArc_on_greatCircle other⟩ ⟨hit, orthogonal⟩

/-- The event that the two arcs have a unique common point. -/
def arcCrossingEvent (u v : Space) (frame : SpatialRotation) (r : ℝ) : Set SpatialRotation :=
  {g | ∃! x ∈ openMinorArc u v, x ∈ linear g '' (linear frame '' equatorialArc r)}

private theorem arcCrossingEvent_preimage (u v : Space) (frame : SpatialRotation) (r : ℝ) :
    arcCrossingEvent u v frame r =
      (fun g => g * frame) ⁻¹'
        {g | ∃! x ∈ openMinorArc u v, x ∈ linear g '' equatorialArc r} := by
  ext g
  simp only [arcCrossingEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.image_image, linear_mul,
    LinearMap.coe_comp, Function.comp_apply]

/-- With both fixed endpoints off the moving great circle, any common point
of the two arcs is their unique intersection. -/
theorem mem_arcCrossingEvent_of_hit {u v x : Space} {g frame : SpatialRotation} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (first : inner ℝ (linear (g * frame) equatorPole) u ≠ 0)
    (last : inner ℝ (linear (g * frame) equatorPole) v ≠ 0)
    (arc : x ∈ openMinorArc u v) (hit : x ∈ linear g '' (linear frame '' equatorialArc r)) :
    g ∈ arcCrossingEvent u v frame r := by
  have images : linear g '' (linear frame '' equatorialArc r) =
      linear (g * frame) '' equatorialArc r := by
    rw [Set.image_image]
    rw [linear_mul, LinearMap.coe_comp]
    rfl
  have on_plane := rotated_equatorialArc_on_greatCircle (images ▸ hit)
  have sign := spatialSignChange_of_minorArc_on_greatCircle hu hv not_antipodal
    first last arc on_plane
  have unique := (minorArc_greatCircle_crossing_iff hu hv not_antipodal first last).mpr sign
  exact ⟨x, ⟨arc, hit⟩, fun _ h =>
    unique.unique ⟨h.1, rotated_equatorialArc_on_greatCircle (images ▸ h.2)⟩ ⟨arc, on_plane⟩⟩

/-- A fixed unit point is almost surely off the great circle of any framed rotating arc. -/
theorem ae_not_on_moving_arc_circle {w : Space} (unit : ‖w‖ = 1) (frame : SpatialRotation) :
    ∀ᵐ g ∂probability, inner ℝ (linear (g * frame) equatorPole) w ≠ 0 := by
  have nonzero : innerSL ℝ w ≠ 0 := by
    intro zero
    have equal := DFunLike.congr_fun zero w
    change inner ℝ w w = 0 at equal
    rw [real_inner_self_eq_norm_sq, unit] at equal
    norm_num at equal
  have unit_pole : ‖linear frame equatorPole‖ = 1 :=
    ((isometry frame).norm_map equatorPole).trans equatorPole_unit
  have null := probability_linear_hyperplane unit_pole (innerSL ℝ w) nonzero
  change probability {g | inner ℝ w (linear g (linear frame equatorPole)) = 0} = 0 at null
  simp only [ae_iff, not_not, linear_mul, LinearMap.comp_apply, real_inner_comm w _]
  exact null

private theorem crossingEvent_ae_eq {u v : Space} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0) :
    {g | ∃! x ∈ openMinorArc u v, x ∈ linear g '' equatorialArc r} =ᵐ[probability]
      crossingRots u v ∩ crossingPhase u v ⁻¹' Metric.closedBall (0 : EquatorPhase) r := by
  have generic {w : Space} (hw : ‖w‖ = 1) :
      ∀ᵐ g ∂probability, inner ℝ (linear g equatorPole) w ≠ 0 := by
    simpa only [mul_one] using ae_not_on_moving_arc_circle hw 1
  filter_upwards [generic hu, generic hv] with g first last
  exact propext (minorArc_equatorialArc_crossing_iff hu hv not_antipodal first last)

/-- The geometric crossing event is measurable up to the null endpoint incidences. -/
theorem nullMeasurableSet_arcCrossingEvent {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) (frame : SpatialRotation) (r : ℝ) :
    NullMeasurableSet (arcCrossingEvent u v frame r) probability := by
  have measurable : MeasurableSet
      (crossingRots u v ∩ crossingPhase u v ⁻¹' Metric.closedBall (0 : EquatorPhase) r) :=
    (crossingRots_measurable u v).inter
      (measurableSet_closedBall.preimage (crossingPhase_measurable u v))
  rw [arcCrossingEvent_preimage]
  exact (measurable.nullMeasurableSet.congr
    (crossingEvent_ae_eq hu hv not_antipodal).symm).preimage
      (measurePreserving_mul_right probability frame).quasiMeasurePreserving

/-- Finite-arc spherical Crofton. The expected crossing count of a fixed
minor arc and a uniformly rotated arc of length (2r) is their length
product divided by (2π^2). Outside the null endpoint incidences the count
is either zero or one. -/
theorem probability_minorArc_equatorialArc {u v : Space} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (nonnegative : 0 ≤ r) (small : r ≤ Real.pi) :
    probability {g | ∃! x ∈ openMinorArc u v, x ∈ linear g '' equatorialArc r} =
      ENNReal.ofReal (angle u v * (2 * r) / (2 * Real.pi ^ 2)) := by
  let E := crossingRots u v ∩
    crossingPhase u v ⁻¹' Metric.closedBall (0 : EquatorPhase) r
  have measurable : MeasurableSet E :=
    (crossingRots_measurable u v).inter
      (measurableSet_closedBall.preimage (crossingPhase_measurable u v))
  have ae_equal := crossingEvent_ae_eq (r := r) hu hv not_antipodal
  have flag : arcCrossing u v r = E.indicator (fun _ => 1) := by
    funext g
    by_cases cross : g ∈ crossingRots u v <;>
      by_cases phase : crossingPhase u v g ∈ Metric.closedBall (0 : EquatorPhase) r <;>
      simp [arcCrossing, E, cross, phase]
  rw [measure_congr ae_equal, ← lintegral_arcCrossing hu hv not_antipodal nonnegative small,
    flag, lintegral_indicator measurable, lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- The moving arc can have any fixed initial spatial frame. Haar probability
absorbs the change of frame by right translation. -/
theorem probability_minorArc_rotated_equatorialArc {u v : Space} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (nonnegative : 0 ≤ r) (small : r ≤ Real.pi) (frame : SpatialRotation) :
    probability {g | ∃! x ∈ openMinorArc u v, x ∈ linear g '' (linear frame '' equatorialArc r)} =
      ENNReal.ofReal (angle u v * (2 * r) / (2 * Real.pi ^ 2)) := by
  change probability (arcCrossingEvent u v frame r) = _
  rw [arcCrossingEvent_preimage, measure_preimage_mul_right probability frame]
  exact probability_minorArc_equatorialArc hu hv not_antipodal nonnegative small

end Unfoldings.SpatialRotation
