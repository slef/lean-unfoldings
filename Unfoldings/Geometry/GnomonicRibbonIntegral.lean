module

public import Unfoldings.Geometry.GnomonicAreaPrimitive
public import Mathlib.MeasureTheory.Integral.Prod

/-! Signed solid-angle integration between two graphs in horizontal normal coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real MeasureTheory

/-- The gnomonic area density on Cartesian coordinates. -/
def cartesianGnomonicDensity (z : ℝ × ℝ) : ℝ :=
  1 / (√(1 + z.1 ^ 2 + z.2 ^ 2)) ^ 3

theorem continuous_cartesianGnomonicDensity : Continuous cartesianGnomonicDensity := by
  unfold cartesianGnomonicDensity
  apply continuous_const.div (by fun_prop)
  intro z
  exact pow_ne_zero _ (sqrt_pos.mpr (by positivity)).ne'

/-- Use a half-open ribbon so its vertical sections are exactly oriented
interval integrals, even if the two graphs exchange order. -/
def graphRibbon (lo hi : ℝ → ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Set.Ioc a b ∧ z.2 ∈ Set.Ioc (lo z.1) (hi z.1)}

theorem measurableSet_graphRibbon {lo hi : ℝ → ℝ} (lower : Measurable lo)
    (upper : Measurable hi) (a b : ℝ) : MeasurableSet (graphRibbon lo hi a b) :=
  measurableSet_region_between_oc lower upper measurableSet_Ioc

/-- Positive winding is the ribbon above the trace; negative winding is the
ribbon below it. Both choices use the same density. -/
def signedGnomonicRibbon (trace chord : ℝ → ℝ) (a b : ℝ) : ℝ × ℝ → ℝ :=
  (graphRibbon trace chord a b).indicator cartesianGnomonicDensity -
    (graphRibbon chord trace a b).indicator cartesianGnomonicDensity

private theorem integrable_graphRibbon {lo hi : ℝ → ℝ} (lower : Continuous lo)
    (upper : Continuous hi) (a b : ℝ) :
    Integrable ((graphRibbon lo hi a b).indicator cartesianGnomonicDensity)
      (volume.prod volume) := by
  rw [integrable_indicator_iff (measurableSet_graphRibbon lower.measurable upper.measurable a b)]
  let block := Set.Icc a b
  let bound := (lo '' block) ∪ (hi '' block)
  have compact : IsCompact bound :=
    (isCompact_Icc.image lower).union (isCompact_Icc.image upper)
  obtain ⟨r, hr⟩ := compact.isBounded.subset_closedBall (0 : ℝ)
  have contained : graphRibbon lo hi a b ⊆ block ×ˢ Set.Icc (-r) r := by
    rintro ⟨p, q⟩ ⟨hp, hq⟩
    have hp' : p ∈ block := Set.Ioc_subset_Icc_self hp
    have l : lo p ∈ Metric.closedBall 0 r := hr (Or.inl ⟨p, hp', rfl⟩)
    have u : hi p ∈ Metric.closedBall 0 r := hr (Or.inr ⟨p, hp', rfl⟩)
    simp only [Metric.mem_closedBall, Real.dist_0_eq_abs, abs_le] at l u
    exact ⟨hp', l.1.trans hq.1.le, hq.2.trans u.2⟩
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    continuous_cartesianGnomonicDensity.continuousOn |>.mono_set contained

/-- Fubini reduces the signed solid angle of a graph ribbon to the difference
of its two connection-form integrals. The graphs may cross. -/
theorem integral_signedGnomonicRibbon {trace chord : ℝ → ℝ} (htrace : Continuous trace)
    (hchord : Continuous chord) {a b : ℝ} (order : a ≤ b) :
    (∫ z, signedGnomonicRibbon trace chord a b z ∂(volume.prod volume)) =
      ∫ p in a..b, gnomonicAreaPrimitive p (chord p) - gnomonicAreaPrimitive p (trace p) := by
  have integrable : Integrable (signedGnomonicRibbon trace chord a b) (volume.prod volume) :=
    (integrable_graphRibbon htrace hchord a b).sub
    (integrable_graphRibbon hchord htrace a b)
  rw [integral_prod _ integrable, intervalIntegral.integral_of_le order,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  refine .of_forall (fun p => ?_)
  let density (q : ℝ) := cartesianGnomonicDensity (p, q)
  have density_cont : Continuous density :=
    continuous_cartesianGnomonicDensity.comp (continuous_const.prodMk continuous_id)
  by_cases hp : p ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hp]
    have slice (lo hi : ℝ → ℝ) :
        (fun q => (graphRibbon lo hi a b).indicator cartesianGnomonicDensity (p, q)) =
          (Set.Ioc (lo p) (hi p)).indicator density := by
      funext q
      by_cases hq : q ∈ Set.Ioc (lo p) (hi p)
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show (p, q) ∈ graphRibbon lo hi a b from
          ⟨hp, hq⟩)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (fun h : (p, q) ∈ graphRibbon lo hi a b => hq h.2)]
    change (∫ q, ((fun t => (graphRibbon trace chord a b).indicator cartesianGnomonicDensity (p, t)) -
      (fun t => (graphRibbon chord trace a b).indicator cartesianGnomonicDensity (p, t))) q) = _
    rw [slice trace chord, slice chord trace]
    simp only [Pi.sub_apply]
    rw [integral_sub
      ((integrable_indicator_iff measurableSet_Ioc).mpr
        (density_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self))
      ((integrable_indicator_iff measurableSet_Ioc).mpr
        (density_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)),
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
    exact integral_gnomonicArea_vertical p (trace p) (chord p)
  · rw [Set.indicator_of_notMem hp]
    have zero (q : ℝ) : signedGnomonicRibbon trace chord a b (p, q) = 0 := by
      simp only [signedGnomonicRibbon, Pi.sub_apply]
      rw [Set.indicator_of_notMem (fun h : (p, q) ∈ graphRibbon trace chord a b => hp h.1),
        Set.indicator_of_notMem (fun h : (p, q) ∈ graphRibbon chord trace a b => hp h.1), sub_self]
    simp [zero]

end Unfoldings
