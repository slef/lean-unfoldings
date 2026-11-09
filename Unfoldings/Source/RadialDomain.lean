module

public import Unfoldings.Source.Domain
public import Unfoldings.Source.SampleLine
public import Unfoldings.Source.Prefixes

/-!
# The constructed source-vector image is star-shaped

Prefixes of actual shortest paths have exactly the scaled initial vector.
This proves radial coverage of the entire planar image, including zero and
full time, without selecting a path at tied endpoints.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

theorem coordinate_initial (p : SourcePath source) (t : unitInterval) :
    R.coordinate (p.initial t).path (p.initial t).geodesic =
      (t : ℝ) • R.coordinate p.path p.geodesic := by
  let q := p.initial t
  let b : unitInterval := min (R.sampleTime q.target) (R.sampleTime p.target)
  have positive : (0 : unitInterval) < b :=
    lt_min (R.sampleTime_pos q.target) (R.sampleTime_pos p.target)
  have before_q : b ≤ R.sampleTime q.target := min_le_left _ _
  let a := Path.intervalParam 0 t b
  have coefficient : (a : ℝ) = (t : ℝ) * (b : ℝ) := by
    simp only [a, Path.intervalParam, AffineMap.lineMap_apply_ring, Set.Icc.coe_zero]
    ring
  have before_p : a ≤ R.sampleTime p.target := by
    change (a : ℝ) ≤ (R.sampleTime p.target : ℝ)
    rw [coefficient]
    exact (mul_le_of_le_one_left b.property.1 t.property.2).trans (min_le_right _ _)
  have first := R.chart_initial_eq p.geodesic a before_p
  have last := R.chart_initial_eq q.geodesic b before_q
  have same : (R.chart ⟨q.path b, R.initial_inside q.geodesic b before_q⟩).val =
      (R.chart ⟨p.path a, R.initial_inside p.geodesic a before_p⟩).val := rfl
  have scaled := add_right_cancel (last.symm.trans (same.trans first))
  have nonzero : (b : ℝ) ≠ 0 := (show (0 : ℝ) < (b : ℝ) from positive).ne'
  apply smul_right_injective Plane nonzero
  change (b : ℝ) • R.coordinate q.path q.geodesic =
    (b : ℝ) • ((t : ℝ) • R.coordinate p.path p.geodesic)
  rw [smul_smul]
  exact scaled.trans (by rw [coefficient, mul_comm])

theorem zero_mem_domain [CompactSpace X] : (0 : Plane) ∈ R.domain := by
  let p := SourcePath.constant source
  refine ⟨p, norm_eq_zero.mp ?_⟩
  rw [R.norm_coordinate]
  exact dist_self source

theorem smul_mem_domain [CompactSpace X] {z : Plane} (member : z ∈ R.domain)
    (t : unitInterval) : (t : ℝ) • z ∈ R.domain := by
  obtain ⟨p, rfl⟩ := member
  exact ⟨p.initial t, R.coordinate_initial p t⟩

theorem starConvex_domain [CompactSpace X] : StarConvex ℝ (0 : Plane) R.domain := by
  intro z member a b ha hb sum
  let t : unitInterval := ⟨b, hb, by linarith⟩
  simpa only [smul_zero, zero_add] using R.smul_mem_domain member t

end Unfoldings.SourceFrame
