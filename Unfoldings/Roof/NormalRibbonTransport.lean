module

public import Unfoldings.Cap.GnomonicCartesianMeasure
public import Unfoldings.Geometry.GnomonicHingeTransport
public import Unfoldings.Roof.NormalAreaCancellation

/-! Signed winding of a monotone normal trace, in the actual solid-angle measure. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real MeasureTheory

/-- The signed winding of the trace followed by the reversed chord. -/
def normalRibbonWinding (trace chord : ℝ → ℝ) (a b : ℝ) (z : ℝ × ℝ) : ℝ :=
  (graphRibbon trace chord a b).indicator (fun _ => 1) z -
    (graphRibbon chord trace a b).indicator (fun _ => 1) z

theorem abs_normalRibbonWinding_le (trace chord : ℝ → ℝ) (a b : ℝ) (z : ℝ × ℝ) :
    |normalRibbonWinding trace chord a b z| ≤ 1 := by
  classical
  unfold normalRibbonWinding
  by_cases h : z ∈ graphRibbon trace chord a b <;>
    by_cases k : z ∈ graphRibbon chord trace a b <;> simp [h, k]

theorem normalRibbonWinding_nonneg_of_above {trace chord : ℝ → ℝ} {a b : ℝ}
    {z : ℝ × ℝ} (above : trace z.1 < z.2) :
    0 ≤ normalRibbonWinding trace chord a b z := by
  classical
  have outside : z ∉ graphRibbon chord trace a b := fun h => above.not_ge h.2.2
  unfold normalRibbonWinding
  by_cases h : z ∈ graphRibbon trace chord a b <;> simp [h, outside]

theorem normalRibbonWinding_nonpos_of_below {trace chord : ℝ → ℝ} {a b : ℝ}
    {z : ℝ × ℝ} (below : z.2 ≤ trace z.1) :
    normalRibbonWinding trace chord a b z ≤ 0 := by
  classical
  have outside : z ∉ graphRibbon trace chord a b := fun h => below.not_gt h.2.1
  unfold normalRibbonWinding
  by_cases h : z ∈ graphRibbon chord trace a b <;> simp [h, outside]

/-- The rotation assigned to the graph ribbon is its signed solid angle. -/
theorem integral_normalRibbonWinding {trace chord : ℝ → ℝ} (htrace : Continuous trace)
    (hchord : Continuous chord) {a b : ℝ} (order : a ≤ b) :
    (∫ z, normalRibbonWinding trace chord a b z ∂Cap.cartesianSolidAngle) =
      ∫ p in a..b, gnomonicAreaPrimitive p (chord p) - gnomonicAreaPrimitive p (trace p) := by
  unfold Cap.cartesianSolidAngle
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure ℝ).prod volume)
    (f := fun z : ℝ × ℝ => ENNReal.ofReal (cartesianGnomonicDensity z))
    (ENNReal.measurable_ofReal.comp continuous_cartesianGnomonicDensity.measurable)
    (.of_forall (fun _ => ENNReal.ofReal_lt_top)) (normalRibbonWinding trace chord a b)]
  refine (integral_congr_ae (.of_forall ?_)).trans
    (integral_signedGnomonicRibbon htrace hchord order)
  intro z
  rw [ENNReal.toReal_ofReal (Cap.cartesianGnomonicDensity_nonneg z)]
  classical
  unfold normalRibbonWinding signedGnomonicRibbon
  by_cases h : z ∈ graphRibbon trace chord a b <;>
    by_cases k : z ∈ graphRibbon chord trace a b <;>
    simp [h, k, smul_eq_mul]

end Unfoldings
