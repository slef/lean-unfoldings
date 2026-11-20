module

public import Unfoldings.Geometry.SpatialRotationSphere
public import Unfoldings.Geometry.SpatialLune

/-! Crofton for one minor arc and a whole randomly rotated great circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory InnerProductGeometry
open scoped ENNReal

/-- A minor spherical arc parameterized by directions of the open chord. -/
def openMinorArc (u v : Space) : Set Space :=
  {x | ∃ t ∈ Set.Ioo (0 : ℝ) 1, NormedSpace.normalize ((1 - t) • u + t • v) = x}

theorem minorArc_chord_ne_zero {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - t) • u + t • v ≠ 0 := by
  intro zero
  have opposite : (1 - t) • u = -(t • v) := eq_neg_of_add_eq_zero_left zero
  have equal_norm := congrArg norm opposite
  rw [norm_neg, norm_smul, norm_smul, hu, hv, mul_one, mul_one,
    Real.norm_of_nonneg (sub_nonneg.mpr ht.2.le), Real.norm_of_nonneg ht.1.le] at equal_norm
  have half : t = 1 / 2 := by linarith
  rw [half, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← smul_add] at zero
  exact not_antipodal ((smul_eq_zero.mp zero).resolve_left (by norm_num))

private theorem chord_equator_iff {n u v : Space} {t : ℝ}
    (nonzero : (1 - t) • u + t • v ≠ 0) :
    inner ℝ n (NormedSpace.normalize ((1 - t) • u + t • v)) = 0 ↔
      (1 - t) * inner ℝ n u + t * inner ℝ n v = 0 := by
  rw [NormedSpace.normalize, real_inner_smul_right, mul_eq_zero,
    or_iff_right (inv_ne_zero (norm_ne_zero_iff.mpr nonzero)), inner_add_right,
    real_inner_smul_right, real_inner_smul_right]

/-- The explicit intersection point, used when the signs at the arc endpoints differ. -/
def minorArcCrossingPoint (n u v : Space) : Space :=
  let a := inner ℝ n u
  let b := inner ℝ n v
  let t := a / (a - b)
  NormedSpace.normalize ((1 - t) • u + t • v)

theorem minorArcCrossingPoint_measurable (u v : Space) :
    Measurable (fun n => minorArcCrossingPoint n u v) := by
  let a (n : Space) := inner ℝ n u
  let b (n : Space) := inner ℝ n v
  have ma : Measurable a := (continuous_id.inner continuous_const).measurable
  have mb : Measurable b := (continuous_id.inner continuous_const).measurable
  let k (n : Space) := a n / (a n - b n)
  have mk : Measurable k := ma.div (ma.sub mb)
  let z (n : Space) := (1 - k n) • u + k n • v
  have first : Measurable (fun n : Space => 1 - k n) := measurable_const.sub mk
  have mz : Measurable z := (first.smul_const u).add (mk.smul_const v)
  have mi : Measurable (fun n : Space => ‖z n‖⁻¹) := mz.norm.inv
  exact mi.smul mz

theorem minorArcCrossingPoint_spec {n u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) (sign : n ∈ spatialSignChange u v) :
    minorArcCrossingPoint n u v ∈ openMinorArc u v ∧
      inner ℝ n (minorArcCrossingPoint n u v) = 0 ∧ ‖minorArcCrossingPoint n u v‖ = 1 := by
  let a := inner ℝ n u
  let b := inner ℝ n v
  change a * b < 0 at sign
  have different : a - b ≠ 0 := by
    intro eq
    rw [sub_eq_zero.mp eq] at sign
    exact (not_lt_of_ge (mul_self_nonneg b)) sign
  let t := a / (a - b)
  have ht : t ∈ Set.Ioo 0 1 := by
    rcases mul_neg_iff.mp sign with ⟨apos, bneg⟩ | ⟨aneg, bpos⟩
    · have denom : 0 < a - b := by linarith
      exact ⟨div_pos apos denom, (div_lt_one denom).mpr (by linarith)⟩
    · have denom : a - b < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg aneg denom, (div_lt_iff_of_neg denom).mpr (by linarith)⟩
  have nonzero := minorArc_chord_ne_zero hu hv not_antipodal ht
  have equal : (1 - t) * a + t * b = 0 := by
    dsimp [t]
    field_simp [different]
    ring
  exact ⟨⟨t, ht, rfl⟩, (chord_equator_iff nonzero).mpr equal, NormedSpace.norm_normalize nonzero⟩

theorem spatialSignChange_of_minorArc_on_greatCircle {n u v x : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (first : inner ℝ n u ≠ 0) (last : inner ℝ n v ≠ 0)
    (arc : x ∈ openMinorArc u v) (orthogonal : inner ℝ n x = 0) :
    n ∈ spatialSignChange u v := by
  let a := inner ℝ n u
  let b := inner ℝ n v
  change a * b < 0
  obtain ⟨t, ht, rfl⟩ := arc
  have zero : (1 - t) * a + t * b = 0 :=
    (chord_equator_iff (minorArc_chord_ne_zero hu hv not_antipodal ht)).mp orthogonal
  by_contra not_change
  have h := le_of_not_gt not_change
  rcases mul_nonneg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have first_positive := lt_of_le_of_ne ha (Ne.symm first)
    have positive := mul_pos (sub_pos.mpr ht.2) first_positive
    linarith [mul_nonneg ht.1.le hb]
  · have first_negative := lt_of_le_of_ne ha first
    have negative := mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) first_negative
    linarith [mul_nonpos_of_nonneg_of_nonpos ht.1.le hb]

/-- Away from endpoint incidences, a great circle meets a minor arc in
exactly one point if its endpoint signs disagree, and misses it otherwise. -/
theorem minorArc_greatCircle_crossing_iff {n u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) (first : inner ℝ n u ≠ 0) (last : inner ℝ n v ≠ 0) :
    (∃! x ∈ openMinorArc u v, inner ℝ n x = 0) ↔ n ∈ spatialSignChange u v := by
  let a := inner ℝ n u
  let b := inner ℝ n v
  change (∃! x, x ∈ openMinorArc u v ∧ inner ℝ n x = 0) ↔ a * b < 0
  constructor
  · rintro ⟨x, ⟨arc, orthogonal⟩, _⟩
    exact spatialSignChange_of_minorArc_on_greatCircle hu hv not_antipodal
      first last arc orthogonal
  · intro sign
    let x := minorArcCrossingPoint n u v
    obtain ⟨arc, equator, _unit⟩ := minorArcCrossingPoint_spec hu hv not_antipodal sign
    change a * b < 0 at sign
    have different : a - b ≠ 0 := by
      intro eq
      rw [sub_eq_zero.mp eq] at sign
      exact (not_lt_of_ge (mul_self_nonneg b)) sign
    have arc' := arc
    obtain ⟨t, ht, point⟩ := arc'
    have in_plane_t : inner ℝ n (NormedSpace.normalize ((1 - t) • u + t • v)) = 0 := by
      rwa [point]
    have equal : (1 - t) * a + t * b = 0 :=
      (chord_equator_iff (minorArc_chord_ne_zero hu hv not_antipodal ht)).mp in_plane_t
    refine ⟨x, ⟨arc, equator⟩, ?_⟩
    rintro _ ⟨⟨s, hs, rfl⟩, in_plane⟩
    have other : (1 - s) * a + s * b = 0 :=
      (chord_equator_iff (minorArc_chord_ne_zero hu hv not_antipodal hs)).mp in_plane
    have product : (s - t) * (a - b) = 0 := by nlinarith only [equal, other]
    rw [sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right different)]
    exact point

namespace SpatialRotation

/-- The rotated equator's two strict endpoint signs disagree with probability
given by the original angular length divided by π. -/
theorem probability_spatialSignChange {n u v : Space}
    (hn : ‖n‖ = 1) (u_ne : u ≠ 0) (v_ne : v ≠ 0) :
    probability ((fun g => linear g n) ⁻¹' spatialSignChange u v) =
      ENNReal.ofReal (angle u v / Real.pi) := by
  have evaluation : Measurable (fun g : SpatialRotation => linear g n) :=
    (continuous_apply.comp (continuous_id.prodMk continuous_const)).measurable
  rw [← Measure.map_apply evaluation
    (spatialSignChange_measurable u v), map_linear_probability hn, uniformSphere, Measure.smul_apply,
    solidAngleMeasure_spatialSignChange u v u_ne v_ne]
  change (ENNReal.ofReal (4 * Real.pi))⁻¹ * ENNReal.ofReal (4 * angle u v) =
    ENNReal.ofReal (angle u v / Real.pi)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < (4 : ℝ) * Real.pi),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- A Haar-rotated great circle crosses a fixed minor arc with probability
equal to its angular length divided by π. -/
theorem probability_minorArc_greatCircle {n u v : Space}
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0) :
    probability {g | ∃! x ∈ openMinorArc u v, inner ℝ (linear g n) x = 0} =
      ENNReal.ofReal (angle u v / Real.pi) := by
  have u_ne : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  have v_ne : v ≠ 0 := norm_ne_zero_iff.mp (by simp [hv])
  have nonzero (w : Space) (hw : w ≠ 0) : innerSL ℝ w ≠ 0 := by
    intro zero
    have value := congrArg (fun f : Space →L[ℝ] ℝ => f w) zero
    change inner ℝ w w = 0 at value
    exact hw (inner_self_eq_zero.mp value)
  have generic (w : Space) (hw : w ≠ 0) : ∀ᵐ g ∂probability, inner ℝ (linear g n) w ≠ 0 := by
    have null := probability_linear_hyperplane hn (innerSL ℝ w) (nonzero w hw)
    change probability {g | inner ℝ w (linear g n) = 0} = 0 at null
    simpa only [ae_iff, not_not, real_inner_comm _ w] using null
  have equivalence : {g | ∃! x ∈ openMinorArc u v, inner ℝ (linear g n) x = 0} =ᵐ[probability]
      ((fun g => linear g n) ⁻¹' spatialSignChange u v) := by
    filter_upwards [generic u u_ne, generic v v_ne] with g first last
    exact propext (minorArc_greatCircle_crossing_iff hu hv not_antipodal first last)
  rw [measure_congr equivalence, probability_spatialSignChange hn u_ne v_ne]

end SpatialRotation
end Unfoldings
