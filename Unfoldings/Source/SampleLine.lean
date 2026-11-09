module

public import Unfoldings.Source.Coordinates

/-! Exact initial straightness for the constructed full-length source vector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source target : X}
  (R : SourceFrame source) {p : Path source target}

theorem chart_initial_eq (geodesic : p.IsGeodesic) (t : unitInterval)
    (before : t ≤ R.sampleTime target) :
    (R.chart ⟨p t, R.initial_inside geodesic t before⟩).val =
      (t : ℝ) • R.coordinate p geodesic + R.origin := by
  let ε := R.sampleTime target
  have positive : (0 : unitInterval) < ε := R.sampleTime_pos target
  let v := Path.intervalFraction 0 ε t positive ⟨t.property.1, before⟩
  have point : Path.intervalParam 0 ε v = t :=
    Path.intervalParam_fraction 0 ε t positive ⟨t.property.1, before⟩
  have straight := geodesic.chart_subpath_eq_lineMap R.chart positive.le
    (fun s hs => R.initial_inside geodesic s hs.2) v
  simp only [point] at straight
  have first : (R.chart ⟨p 0, R.initial_inside geodesic 0 positive.le⟩).val = R.origin :=
    congrArg (fun z => (R.chart z).val) (Subtype.ext p.source)
  have parameter : (v : ℝ) = (t : ℝ) / (ε : ℝ) := by
    simp only [v, Path.intervalFraction, Set.Icc.coe_zero, sub_zero]
  rw [first, AffineMap.lineMap_apply_module', parameter] at straight
  exact straight.trans (by rw [div_eq_mul_inv, mul_smul]; rfl)

end Unfoldings.SourceFrame
