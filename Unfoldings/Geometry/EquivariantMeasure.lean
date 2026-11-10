module

public import Mathlib.MeasureTheory.Group.Measure

/-! Equivariance almost everywhere transports invariant measures to a group. -/

@[expose] public section

namespace Unfoldings

open MeasureTheory

variable {X G : Type*} [MeasurableSpace X] [AddGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G]

/-- An almost-equivariant observable of measure-preserving shifts has translation-invariant law. -/
theorem isAddLeftInvariant_map_of_ae_equivariant (μ : Measure X) (f : X → G)
    (measurable : Measurable f) (shift : G → X → X)
    (preserving : ∀ g, MeasurePreserving (shift g) μ μ)
    (equivariant : ∀ g, ∀ᵐ x ∂μ, f (shift g x) = g + f x) :
    (μ.map f).IsAddLeftInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.map_map (measurable_const_add g) measurable]
  calc
    μ.map ((g + ·) ∘ f) = μ.map (f ∘ shift g) :=
      Measure.map_congr (Filter.EventuallyEq.symm (equivariant g))
    _ = (μ.map (shift g)).map f :=
      (Measure.map_map measurable (preserving g).measurable).symm
    _ = μ.map f := by rw [(preserving g).map_eq]

end Unfoldings
