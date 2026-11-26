module

public import Unfoldings.Geometry.GnomonicHingeFrame
public import Unfoldings.Roof.NormalRibbonTransport

/-! The hinge corrections telescope against the signed ribbon of an actual polygonal normal trace. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real MeasureTheory
open scoped BigOperators

/-- The change of the real hinge angle along a nonvertical normal segment. -/
def hingeAngleChange (m b first last : ℝ) : ℝ :=
  arctan (gnomonicHingeRatio m b last) - arctan (gnomonicHingeRatio m b first)

private theorem continuous_primitive_trace {trace : ℝ → ℝ} (htrace : Continuous trace) :
    Continuous (fun p => gnomonicAreaPrimitive p (trace p)) := by
  unfold gnomonicAreaPrimitive
  apply htrace.div (by fun_prop)
  intro p
  positivity

/-- The real changes of frame across a polygonal trace add to its full
connection integral. Zero lengths contribute zero. -/
theorem sum_hingeAngleChange_eq_integral {trace : ℝ → ℝ} (htrace : Continuous trace)
    (p m b : ℕ → ℝ) {n : ℕ} (monotone : Monotone p)
    (segments : ∀ i < n, ∀ t ∈ Set.Icc (p i) (p (i + 1)), trace t = m i * t + b i) :
    (∑ i ∈ Finset.range n, hingeAngleChange (m i) (b i) (p i) (p (i + 1))) =
      ∫ t in p 0..p n, gnomonicAreaPrimitive t (trace t) := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals (a := p)
    (fun i _ => (continuous_primitive_trace htrace).intervalIntegrable (p i) (p (i + 1)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hingeAngleChange, ← integral_gnomonicHingeAngle]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (monotone (Nat.le_succ i))] at ht
  change gnomonicAreaPrimitive t (m i * t + b i) = gnomonicAreaPrimitive t (trace t)
  rw [segments i (Finset.mem_range.mp hi) t ht]

/-- The difference between the direct chord's hinge change and those of the full
trace is its signed solid angle, including traces crossing the chord. -/
theorem hingeChord_sub_trace_eq_winding {trace : ℝ → ℝ} (htrace : Continuous trace)
    (p m b : ℕ → ℝ) {n : ℕ} (monotone : Monotone p)
    (segments : ∀ i < n, ∀ t ∈ Set.Icc (p i) (p (i + 1)), trace t = m i * t + b i)
    (slope intercept : ℝ) :
    hingeAngleChange slope intercept (p 0) (p n) -
      (∑ i ∈ Finset.range n, hingeAngleChange (m i) (b i) (p i) (p (i + 1))) =
        ∫ z, normalRibbonWinding trace (fun t => slope * t + intercept) (p 0) (p n) z
          ∂Cap.cartesianSolidAngle := by
  have hc : Continuous (fun t : ℝ => slope * t + intercept) := by fun_prop
  rw [integral_normalRibbonWinding htrace hc (monotone (Nat.zero_le n)),
    intervalIntegral.integral_sub ((continuous_primitive_trace hc).intervalIntegrable (p 0) (p n))
      ((continuous_primitive_trace htrace).intervalIntegrable (p 0) (p n)),
    sum_hingeAngleChange_eq_integral htrace p m b monotone segments,
    integral_gnomonicHingeAngle, hingeAngleChange]

end Unfoldings
