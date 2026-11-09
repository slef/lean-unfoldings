module

public import Unfoldings.Basic
public import Unfoldings.Metric.BallChart
public import Unfoldings.Path.MetricGeodesic
public import Unfoldings.Path.InitialChart
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Constructed planar coordinates of shortest paths from a regular source

A uniform positive sample time, depending only on endpoint distance, lies in
the actual source ball chart. Extend its straight displacement to the full
constant-speed parameter interval. The resulting vector has norm equal to the
intrinsic path length, and equality of vectors forces initial path agreement.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X]

structure SourceFrame (source : X) where
  radius : ℝ
  positive : 0 < radius
  center : Plane
  chart : Metric.eball source (ENNReal.ofReal radius) ≃ᵢ Metric.ball center radius

theorem exists_sourceFrame {source : X} (regular : HasMetricBallChart Plane source) :
    Nonempty (SourceFrame source) := by
  obtain ⟨r, positive, center, ⟨chart⟩⟩ := regular
  exact ⟨⟨r, positive, center, chart⟩⟩

def sourceFrame {source : X} (regular : HasMetricBallChart Plane source) : SourceFrame source :=
  Classical.choice (exists_sourceFrame regular)

namespace SourceFrame

variable {source : X} (R : SourceFrame source)

def sourcePoint : Metric.eball source (ENNReal.ofReal R.radius) :=
  ⟨source, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr R.positive)⟩

def origin : Plane := (R.chart R.sourcePoint).val

def sampleTime (target : X) : unitInterval :=
  ⟨min (1 / 2 : ℝ) (R.radius / (2 * (dist source target + 1))), by
    constructor
    · exact (lt_min (by norm_num) (div_pos R.positive (by positivity))).le
    · exact (min_le_left _ _).trans (by norm_num)⟩

theorem sampleTime_pos (target : X) : (0 : unitInterval) < R.sampleTime target := by
  change (0 : ℝ) < min _ _
  exact lt_min (by norm_num) (div_pos R.positive (by positivity))

theorem sampleTime_distance (target : X) :
    dist source target * (R.sampleTime target : ℝ) < R.radius := by
  have denominator : 0 < 2 * (dist source target + 1) := by positivity
  have upper : (R.sampleTime target : ℝ) * (2 * (dist source target + 1)) ≤ R.radius :=
    (le_div_iff₀ denominator).mp (min_le_right _ _)
  have positive : 0 < (R.sampleTime target : ℝ) := R.sampleTime_pos target
  nlinarith [dist_nonneg (x := source) (y := target)]

theorem initial_inside {target : X} {p : Path source target} (geodesic : p.IsGeodesic)
    (t : unitInterval) (before : t ≤ R.sampleTime target) :
    p t ∈ Metric.eball source (ENNReal.ofReal R.radius) := by
  rw [Metric.mem_eball, edist_dist]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
  rw [dist_comm, geodesic.dist_source]
  exact (mul_le_mul_of_nonneg_left
    (show (t : ℝ) ≤ (R.sampleTime target : ℝ) from before) dist_nonneg).trans_lt
    (R.sampleTime_distance target)

def samplePoint {target : X} (p : Path source target) (geodesic : p.IsGeodesic) :
    Metric.eball source (ENNReal.ofReal R.radius) :=
  ⟨p (R.sampleTime target), R.initial_inside geodesic _ le_rfl⟩

def coordinate {target : X} (p : Path source target) (geodesic : p.IsGeodesic) : Plane :=
  (R.sampleTime target : ℝ)⁻¹ • ((R.chart (R.samplePoint p geodesic)).val - R.origin)

theorem norm_coordinate {target : X} (p : Path source target) (geodesic : p.IsGeodesic) :
    ‖R.coordinate p geodesic‖ = dist source target := by
  have sample_distance : dist (R.chart (R.samplePoint p geodesic)).val R.origin =
      dist source target * (R.sampleTime target : ℝ) := by
    change dist (R.chart (R.samplePoint p geodesic)) (R.chart R.sourcePoint) = _
    rw [R.chart.isometry.dist_eq]
    change dist (p (R.sampleTime target)) source = _
    rw [dist_comm, geodesic.dist_source]
  have positive : 0 < (R.sampleTime target : ℝ) := R.sampleTime_pos target
  change ‖(R.sampleTime target : ℝ)⁻¹ • _‖ = _
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr positive.le),
    ← dist_eq_norm, sample_distance]
  field_simp

theorem initial_eq_of_coordinate_eq {a b : X} {p : Path source a} {q : Path source b}
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (equal : R.coordinate p geodesic = R.coordinate q other) :
    ∃ ε : unitInterval, 0 < ε ∧ ∀ t ≤ ε, p t = q t := by
  have distance : dist source a = dist source b :=
    (R.norm_coordinate p geodesic).symm.trans
      ((congrArg norm equal).trans (R.norm_coordinate q other))
  have time : R.sampleTime a = R.sampleTime b := by
    apply Subtype.ext
    change min _ (R.radius / (2 * (dist source a + 1))) =
      min _ (R.radius / (2 * (dist source b + 1)))
    rw [distance]
  have positive : 0 < (R.sampleTime a : ℝ) := R.sampleTime_pos a
  have coordinates : (R.chart (R.samplePoint p geodesic)).val =
      (R.chart (R.samplePoint q other)).val := by
    change (R.sampleTime a : ℝ)⁻¹ • _ = (R.sampleTime b : ℝ)⁻¹ • _ at equal
    rw [← time] at equal
    exact sub_left_inj.mp (smul_right_injective Plane (inv_ne_zero positive.ne') equal)
  have sample : p (R.sampleTime a) = q (R.sampleTime a) := by
    have same := congrArg Subtype.val (R.chart.injective (Subtype.ext coordinates))
    change p (R.sampleTime a) = q (R.sampleTime b) at same
    rwa [← time] at same
  refine ⟨R.sampleTime a, R.sampleTime_pos a, ?_⟩
  exact geodesic.eq_initial_of_chart_sample other R.chart (R.sampleTime_pos a)
    (R.initial_inside geodesic) (fun t ht => R.initial_inside other t (by rwa [← time]))
    rfl sample

end SourceFrame
end Unfoldings
