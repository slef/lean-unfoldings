module

public import Unfoldings.FewestNets.SingleCellCrofton

/-! Pair both orthogonal cosets before charging the residual endpoint crossings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory InnerProductGeometry SpatialRotation Real

/-- The central regions cancel in the signed expectation, leaving only
the lengths of the unmarked sides and the individual endpoint reaches. -/
theorem mean_singleCellCharge_le_of_endpoint_witnesses {I J : Type*} [Fintype I] [Fintype J]
    (charge : Bool → SpatialRotation → ℝ) (integrable : ∀ b, Integrable (charge b) probability)
    (central : Bool → J → Set SpatialRotation)
    (measurable : ∀ b j, MeasurableSet (central b j))
    (disjoint : ∀ b, Pairwise fun i j => Disjoint (central b i) (central b j))
    (flip : J → SpatialRotation)
    (stable : ∀ j, ∀ᵐ g ∂probability, g ∈ central false j ↔ g * flip j ∈ central true j)
    (paired : ∀ j, ∀ᵐ g ∂probability, g ∈ central false j →
      charge false g + charge true (g * flip j) = 0)
    (changed : Bool → SpatialRotation → I → Prop) [∀ b g, DecidablePred (changed b g)]
    (u v : Bool → I → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    (hu : ∀ b i, ‖u b i‖ = 1) (hv : ∀ b i, ‖v b i‖ = 1)
    (nonantipodal : ∀ b i, u b i + v b i ≠ 0)
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ π / 2)
    (reach : J × Bool → ℝ) (reach_nonneg : ∀ j, 0 ≤ reach j)
    (S : ℝ) (side_length : ∀ b, (∑ i, angle (u b i) (v b i)) = S)
    (pointwise : ∀ b, ∀ᵐ g ∂probability, g ∈ (⋃ j, central b j)ᶜ →
      charge b g ≤ (∑ i, if changed b g i then (1 : ℝ) else 0) / 4)
    (witness : ∀ b, ∀ᵐ g ∂probability, g ∈ (⋃ j, central b j)ᶜ →
      ∀ i, changed b g i → ∃ (j : J × Bool) (x : Space),
        x ∈ openMinorArc (u b i) (v b i) ∧
        x ∈ linear g '' (linear (frame j.1) '' equatorialArc (radius j.1)) ∧
        angle (linear g (linear (frame j.1) (equatorPoint
          ((arcEndpointPhase (radius j.1) j.2 : ℝ) : EquatorPhase)))) x ≤ reach j) :
    ((∫ g, charge false g ∂probability) + (∫ g, charge true g ∂probability)) / 2 ≤
      S * (∑ j, reach j) / (8 * π ^ 2) := by
  let remaining (b : Bool) := (⋃ j, central b j)ᶜ
  have bound (b : Bool) :
      (∫ g in remaining b, charge b g ∂probability) ≤
        S * (∑ j, reach j) / (8 * π ^ 2) := by
    have estimate := integral_singleCellCharge_le_of_endpoint_witnesses (charge b) (remaining b)
      (changed b) (u b) (v b) frame radius (hu b) (hv b) (nonantipodal b)
      (integrable b) (MeasurableSet.iUnion (measurable b)).compl (pointwise b)
      nonneg small reach reach_nonneg (witness b)
    rwa [side_length b] at estimate
  have cancellation := integral_cosets_eq_of_cancelling_regions central measurable disjoint
    flip charge integrable stable paired
  rw [cancellation]
  linarith only [bound false, bound true]

end Unfoldings.FewestNets
