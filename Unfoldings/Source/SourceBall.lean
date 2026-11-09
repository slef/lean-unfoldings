module

public import Unfoldings.Source.OffCutCoordinates

/-!
# The source coordinates are an actual isometry on the source ball

Every shortest path to a point in the source chart remains in that chart.
Its constructed full-length vector equals the actual endpoint displacement.
Consequently the cut-complement coordinates are isometric on a whole source
ball. Propagating this local metric statement along retained paths is separate.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

theorem coordinate_eq_chart_displacement {target : X} (p : Path source target)
    (geodesic : p.IsGeodesic) (near : target ∈ Metric.eball source (ENNReal.ofReal R.radius)) :
    R.coordinate p geodesic = (R.chart ⟨target, near⟩).val - R.origin := by
  have inside := geodesic.mem_eball source (ENNReal.ofReal R.radius)
    (by simpa only [edist_self, zero_add, Metric.mem_eball, edist_comm] using near)
  have straight := geodesic.chart_eq_lineMap R.chart R.sourcePoint.property near inside
    (R.sampleTime target)
  change (R.chart (R.samplePoint p geodesic)).val =
    AffineMap.lineMap R.origin (R.chart ⟨target, near⟩).val (R.sampleTime target : ℝ) at straight
  rw [AffineMap.lineMap_apply_module'] at straight
  change (R.sampleTime target : ℝ)⁻¹ • _ = _
  rw [straight, add_sub_cancel_right, ← mul_smul,
    inv_mul_cancel₀ (show (R.sampleTime target : ℝ) ≠ 0 from
      (show (0 : ℝ) < (R.sampleTime target : ℝ) from R.sampleTime_pos target).ne'), one_smul]

def chartCoordinates (x : Metric.eball source (ENNReal.ofReal R.radius)) : Plane :=
  (R.chart x).val - R.origin

theorem chartCoordinates_isometry : Isometry R.chartCoordinates := by
  apply Isometry.of_dist_eq
  intro x y
  change dist ((R.chart x).val - R.origin) ((R.chart y).val - R.origin) = dist x y
  rw [dist_sub_right]
  exact R.chart.isometry.dist_eq x y

def sourceBallOffCut (x : Metric.eball source (ENNReal.ofReal R.radius)) :
    ↥((sourceCutLocus source)ᶜ) :=
  ⟨x.val, fun member => R.cutLocus_subset_outside_source_ball member x.property⟩

variable [CompactSpace X]
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

theorem coordinatesOffCutLocus_source_ball (x : Metric.eball source (ENNReal.ofReal R.radius)) :
    R.coordinatesOffCutLocus exists_paths (R.sourceBallOffCut x) = R.chartCoordinates x := by
  let p := (SourcePath.offCutLocusHomeomorph exists_paths).symm (R.sourceBallOffCut x)
  have target : p.val.target = x.val :=
    congrArg Subtype.val ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply _)
  have near : p.val.target ∈ Metric.eball source (ENNReal.ofReal R.radius) :=
    target.symm ▸ x.property
  have equal := R.coordinate_eq_chart_displacement p.val.path p.val.geodesic near
  change R.coordinate p.val.path p.val.geodesic = R.chartCoordinates x
  rw [equal]
  have point : (⟨p.val.target, near⟩ : Metric.eball source (ENNReal.ofReal R.radius)) = x :=
    Subtype.ext target
  rw [point]
  rfl

theorem coordinatesOffCutLocus_source_ball_isometry :
    Isometry (R.coordinatesOffCutLocus exists_paths ∘ R.sourceBallOffCut) := by
  have equal : R.coordinatesOffCutLocus exists_paths ∘ R.sourceBallOffCut = R.chartCoordinates :=
    funext (R.coordinatesOffCutLocus_source_ball exists_paths)
  rw [equal]
  exact R.chartCoordinates_isometry

end Unfoldings.SourceFrame
