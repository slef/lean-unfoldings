module

public import Unfoldings.Roof.NormalPolygonCharges

/-! Cancellation between signed vertex curvature and the closing-link winding. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

open MeasureTheory
open scoped ENNReal BigOperators

/-- The signed curvature and the transport term cost at most one copy of the
selector's solid angle. At every slope on their common support the two signs
agree, as certified by the actual active contacts on a horizontal link. -/
theorem abs_charge_sub_winding_le (E : SlopeEnvelope)
    {V : Type*} [Fintype V] {polygon : V → Set Plane} {cell : Set Plane}
    (compact : IsCompact cell) (finite : Cap.cartesianSolidAngle (Cap.planeCartesian '' cell) < ∞)
    (separated : Pairwise fun v w => Disjoint (interior (polygon v)) (interior (polygon w)))
    (contained : ∀ v, polygon v ⊆ cell) (position : V → Plane)
    (active : ∀ v q, q ∈ polygon v → E.Active (position v) q)
    (level : ℝ) (trace chord : ℝ → ℝ) (htrace : Measurable trace) (hchord : Measurable chord)
    {a b : ℝ}
    (contacts : ∀ p ∈ Set.Ioc a b, ∃ x : Plane, x 1 = level ∧
      E.Active x (WithLp.toLp 2 ![p, trace p]))
    (ribbon : graphRibbon trace chord a b ∪ graphRibbon chord trace a b ⊆ Cap.planeCartesian '' cell)
    (weight : V → ℝ) (bounded : ∀ v, |weight v| ≤ 1)
    (sign : ∀ v, 0 ≤ ((position v) 1 - level) * weight v)
    (on_link : ∀ v, (position v) 1 = level → weight v = 0) :
    |(∫ z, Cap.normalPolygonCharge polygon weight z ∂Cap.cartesianSolidAngle) -
      (∫ z, normalRibbonWinding trace chord a b z ∂Cap.cartesianSolidAngle)| ≤
      (solidAngleMeasure (Cap.gnomonicNormal '' cell)).toReal := by
  classical
  let μ := Cap.cartesianSolidAngle
  let C := Cap.planeCartesian '' cell
  let P (v : V) := Cap.planeCartesian '' interior (polygon v)
  let W := normalRibbonWinding trace chord a b
  let Q := Cap.normalPolygonCharge polygon weight
  have measurable : MeasurableSet C :=
    Cap.planeCartesian.measurableSet_image.mpr compact.measurableSet
  have charge_integrable : Integrable Q μ := Cap.integrable_normalPolygonCharge finite contained _
  have integrable_ribbon {r : Set (ℝ × ℝ)} (m : MeasurableSet r) (sub : r ⊆ C) :
      Integrable (r.indicator (fun _ => (1 : ℝ))) μ := by
    have total := (measure_mono sub).trans_lt finite
    let : IsFiniteMeasure (μ.restrict r) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact (integrable_indicator_iff m).mpr (integrable_const _)
  have ribbon_integrable : Integrable W μ :=
    (integrable_ribbon (measurableSet_graphRibbon htrace hchord a b)
      (Set.subset_union_left.trans ribbon)).sub
      (integrable_ribbon (measurableSet_graphRibbon hchord htrace a b)
        (Set.subset_union_right.trans ribbon))
  have qsingle {z : ℝ × ℝ} {v : V} (hz : z ∈ P v) : Q z = weight v := by
    unfold Q Cap.normalPolygonCharge
    rw [Finset.sum_eq_single v, Set.indicator_of_mem hz]
    · intro w _ different
      refine Set.indicator_of_notMem (fun hw => ?_) _
      obtain ⟨p, hp, rfl⟩ := hz
      obtain ⟨q, hq, same⟩ := hw
      have eq : q = p := Cap.planeCartesian.injective same
      exact (Set.disjoint_left.mp (separated different)) (eq ▸ hq) hp
    · exact (fun contrary => (contrary (Finset.mem_univ v)).elim)
  have qzero {z : ℝ × ℝ} (outside : ∀ v, z ∉ P v) : Q z = 0 := by
    exact Finset.sum_eq_zero (fun v _ => Set.indicator_of_notMem (outside v) _)
  have wzero {z : ℝ × ℝ} (out : z ∉ graphRibbon trace chord a b ∪ graphRibbon chord trace a b) :
      W z = 0 := by
    have l : z ∉ graphRibbon trace chord a b := fun h => out (Or.inl h)
    have r : z ∉ graphRibbon chord trace a b := fun h => out (Or.inr h)
    simp [W, normalRibbonWinding, l, r]
  have pointwise (z : ℝ × ℝ) : |Q z| ≤ 1 ∧ |W z| ≤ 1 ∧ 0 ≤ Q z * W z := by
    have wbound : |W z| ≤ 1 := abs_normalRibbonWinding_le _ _ _ _ _
    by_cases nonzero : ∃ v, z ∈ P v
    · obtain ⟨v, inside⟩ := nonzero
      rw [qsingle inside]
      refine ⟨bounded v, wbound, ?_⟩
      by_cases outside : z ∉ graphRibbon trace chord a b ∪ graphRibbon chord trace a b
      · rw [wzero outside, mul_zero]
      · obtain ⟨q, member, rfl⟩ := inside
        have range : q 0 ∈ Set.Ioc a b := by
          rcases not_not.mp outside with h | h <;>
            simpa only [Cap.planeCartesian_apply] using h.1
        obtain ⟨x, on, contact⟩ := contacts (q 0) range
        by_cases eq : (position v) 1 = level
        · rw [on_link v eq, zero_mul]
        · apply E.vertex_charge_mul_winding_nonneg contact (active v) member rfl rfl
          · exact fun h => eq (h.symm.trans on)
          · simpa only [on] using sign v
    · rw [qzero (not_exists.mp nonzero), zero_mul, abs_zero]
      exact ⟨zero_le_one, wbound, le_rfl⟩
  have outside {z : ℝ × ℝ} (away : z ∉ C) : Q z = 0 ∧ W z = 0 :=
    ⟨qzero (fun v hz => away (Set.image_mono (interior_subset.trans (contained v)) hz)),
      wzero (fun h => away (ribbon h))⟩
  have bound := abs_integral_sub_le_measure_of_same_sign measurable finite charge_integrable
    ribbon_integrable (.of_forall pointwise) (.of_forall (fun _ => outside))
  simpa only [Measure.real, C, μ, Cap.cartesianSolidAngle_image compact, Q, W] using bound

end Unfoldings.SlopeEnvelope
