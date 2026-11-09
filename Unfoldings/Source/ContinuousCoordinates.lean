module

public import Unfoldings.Source.Coordinates
public import Unfoldings.Source.CompactPaths

/-! The constructed source coordinates vary continuously with the entire shortest path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

theorem continuous_sampleTime : Continuous R.sampleTime := by
  apply Continuous.subtype_mk
  exact continuous_const.min (continuous_const.div
    (continuous_const.mul ((continuous_const.dist continuous_id).add continuous_const))
    (fun target => ne_of_gt (by positivity)))

theorem continuous_samplePoint : Continuous (fun p : SourcePath source =>
    R.samplePoint p.path p.geodesic) := by
  apply Continuous.subtype_mk
  exact SourcePath.continuous_evaluation.comp
    (continuous_id.prodMk (R.continuous_sampleTime.comp SourcePath.continuous_target))

theorem continuous_coordinate : Continuous (fun p : SourcePath source =>
    R.coordinate p.path p.geodesic) := by
  have time : Continuous (fun p : SourcePath source => (R.sampleTime p.target : ℝ)) :=
    continuous_subtype_val.comp (R.continuous_sampleTime.comp SourcePath.continuous_target)
  have nonzero (p : SourcePath source) : (R.sampleTime p.target : ℝ) ≠ 0 :=
    (show (0 : ℝ) < (R.sampleTime p.target : ℝ) from R.sampleTime_pos p.target).ne'
  exact (time.inv₀ nonzero).smul
    ((continuous_subtype_val.comp (R.chart.continuous.comp R.continuous_samplePoint)).sub
      continuous_const)

theorem compact_coordinate_range [CompactSpace X] :
    IsCompact (Set.range (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :=
  isCompact_range R.continuous_coordinate

end Unfoldings.SourceFrame
