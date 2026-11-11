module

public import Unfoldings.Geometry.MonotoneStripCore
public import Unfoldings.Geometry.RecoverableStripPinches

/-! Injectivity across reopening pinches requires continuity only at their coherent values. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem injOn_strict_of_recoverable_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j) (E : Set ℂ) (a b : ℝ)
    (pinches : S.RecoverablePinchesIn E a b) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧
      z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z) :
    Set.InjOn F {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  intro p hp q hq equal
  let c := max (p.re + p.im) (q.re + q.im)
  have cb : c ≤ b := max_le hp.2.2 hq.2.2
  have positive_end : S.lower.coordinate c < S.upper.coordinate c := by
    rcases le_total (p.re + p.im) (q.re + q.im) with ordered | ordered
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_right ordered]
      exact hq.1.1.trans hq.1.2
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_left ordered]
      exact hp.1.1.trans hp.1.2
  have inside : {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a c} ⊆
      {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧ z.re + z.im ∈ Set.Icc a b} := by
    intro z member
    have slab : z.re + z.im ∈ Set.Icc a b :=
      ⟨member.2.1, member.2.2.trans cb⟩
    refine ⟨?_, slab⟩
    rcases member.1.2 with strict | collapsed
    · exact Or.inl strict
    · have coherent := pinches _ slab collapsed c ⟨member.2.2, cb⟩ positive_end
      have point : S.lower.point (z.re + z.im) = z :=
        S.lower.point_eq_of_coordinate z
          (le_antisymm member.1.1.1 (member.1.1.2.trans_eq collapsed.symm))
      exact Or.inr (point ▸ coherent)
  have injective := S.injOn_strict_of_core_affine_selection A continuous positive a c
    (Fcontinuous.mono inside)
    (fun z member slab => selection z (inside ⟨member, slab⟩).1 (inside ⟨member, slab⟩).2)
  exact injective ⟨hp.1, hp.2.1, le_max_left _ _⟩
    ⟨hq.1, hq.2.1, le_max_right _ _⟩ equal

end Unfoldings.MonotoneStrip
