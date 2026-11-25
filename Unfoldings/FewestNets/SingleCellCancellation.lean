module

public import Unfoldings.FewestNets.SingleCellCharge
public import Unfoldings.Geometry.SpatialRotationMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral

/-! Cancel signed contributions on the central rotations of a selector side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SingleCellCharge

open MeasureTheory SpatialRotation

/-- Right multiplication pairs opposite charges on a stable set of rotations. -/
theorem integral_central_eq_zero (central : Set SpatialRotation) (flip : SpatialRotation)
    (stable : ∀ᵐ g ∂probability, g * flip ∈ central ↔ g ∈ central)
    (a : SpatialRotation → ℝ)
    (opposite : ∀ᵐ g ∂probability, g ∈ central → a (g * flip) + a g = 0) :
    ∫ g, central.indicator a g ∂probability = 0 := by
  let restricted := central.indicator a
  have negate : (fun g => restricted (g * flip)) =ᵐ[probability] fun g => -restricted g := by
    filter_upwards [stable, opposite] with g stays paired
    by_cases inside : g ∈ central
    · have after := stays.mpr inside
      simp only [restricted, Set.indicator_of_mem inside, Set.indicator_of_mem after]
      linarith only [paired inside]
    · have after : g * flip ∉ central := fun member => inside (stays.mp member)
      simp [restricted, Set.indicator_of_notMem inside, Set.indicator_of_notMem after]
  have same : (∫ g, restricted (g * flip) ∂probability) = ∫ g, restricted g ∂probability :=
    (measurePreserving_mul_right probability flip).integral_comp
      (MeasurableEquiv.mulRight flip).measurableEmbedding restricted
  rw [integral_congr_ae negate, integral_neg] at same
  exact neg_eq_self.mp same

/-- A countable disjoint collection of cancelling rotation sets can be discarded
before bounding the expected charge. -/
theorem integral_eq_of_cancelling_central_regions {I : Type*} [Countable I]
    (central : I → Set SpatialRotation) (measurable : ∀ i, MeasurableSet (central i))
    (disjoint : Pairwise fun i j => Disjoint (central i) (central j))
    (a : SpatialRotation → ℝ) (integrable : Integrable a probability)
    (cancel : ∀ i, (∫ g, (central i).indicator a g ∂probability) = 0) :
    ∫ g, a g ∂probability = ∫ g, ((⋃ i, central i)ᶜ).indicator a g ∂probability := by
  classical
  have union : MeasurableSet (⋃ i, central i) := MeasurableSet.iUnion measurable
  have zero : (∫ g in ⋃ i, central i, a g ∂probability) = 0 := by
    have vanishes (i : I) : (∫ g in central i, a g ∂probability) = 0 := by
      rw [← integral_indicator (measurable i)]
      exact cancel i
    rw [integral_iUnion measurable disjoint integrable.integrableOn]
    simp only [vanishes, tsum_zero]
  rw [integral_indicator union.compl]
  rw [← integral_add_compl union integrable, zero, zero_add]

end Unfoldings.FewestNets.SingleCellCharge
