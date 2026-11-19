module

public import Unfoldings.Metric.MappedBankGraft

/-! Exact original cell presentations give exact intrinsic-piece seam classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

section Presentation

variable {I J : Type*} (E : I → Type*) (X : J → Type*)
  [∀ i, EMetricSpace (E i)] [∀ j, EMetricSpace (X j)]
  (raw : Total E → Total E → Prop) (glue : Total X → Total X → Prop)

/-- Exactness descends along a surjective original-cell presentation preserving metric
points and sending every original seam to a declared intrinsic-piece seam chain. -/
theorem exact_of_presentation (restore : Total E → Total X)
    (surjective : Function.Surjective restore)
    (A : Realization E raw ≃ᵢ Realization X glue)
    (points : ∀ a, A (point E raw a) = point X glue (restore a))
    (exact_raw : Exact E raw)
    (compatible : ∀ a b, raw a b → Relation.EqvGen glue (restore a) (restore b)) :
    Exact X glue := by
  intro x y equal
  obtain ⟨a, rfl⟩ := surjective x
  obtain ⟨b, rfl⟩ := surjective y
  have raw_equal : point E raw a = point E raw b := A.injective
    ((points a).trans (equal.trans (points b).symm))
  have related := exact_raw a b raw_equal
  clear equal raw_equal
  induction related with
  | rel a b joined => exact compatible a b joined
  | refl a => exact Relation.EqvGen.refl (restore a)
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ first last => exact Relation.EqvGen.trans _ _ _ first last

end Presentation

variable {I : Type*} {J : I → Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {B : Type*} {Parameter : B → Type*}
  {Ambient : Type*} [MetricSpace Ambient] (cells : ∀ i, J i → Set Ambient)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (coordinates : ∀ i, Realization (fun j => cells i j) (inner i) ≃ᵢ X i)
  (left right : ∀ b, Parameter b → Total X)

/-- Every actual intrinsic piece point has an original underlying cell representative. -/
theorem mappedNestedPoint_surjective :
    Function.Surjective (mappedNestedPoint cells inner coordinates) := by
  rintro ⟨i, x⟩
  obtain ⟨⟨j, p⟩, named⟩ := point_surjective (fun j => cells i j) (inner i)
    ((coordinates i).symm x)
  refine ⟨⟨⟨i, j⟩, p⟩, ?_⟩
  have equal := congrArg (fun q => (⟨i, coordinates i q⟩ : Total X)) named
  simpa only [mappedNestedPoint, of, IsometryEquiv.apply_symm_apply] using equal

/-- Every internal original-cell seam and every marked-bank seam induces a declared
seam chain between intrinsic pieces. Internal seams become literal same-piece equalities. -/
theorem mappedBankGraftCells_eqvGen_image
    (a b : Total (NestedCell (fun i j => cells i j)))
    (joined : mappedBankGraftCells cells inner coordinates left right a b) :
    Relation.EqvGen (bankSeams left right)
      (mappedNestedPoint cells inner coordinates a)
      (mappedNestedPoint cells inner coordinates b) := by
  cases joined with
  | inside i a b seam =>
    have equal := congrArg (fun q => (⟨i, coordinates i q⟩ : Total X))
      (point_eq_of_glue (fun j => cells i j) seam)
    change Relation.EqvGen (bankSeams left right)
      ⟨i, coordinates i (point (fun j => cells i j) (inner i) a)⟩
      ⟨i, coordinates i (point (fun j => cells i j) (inner i) b)⟩
    rw [equal]
    exact Relation.EqvGen.refl _
  | between a b seam => exact Relation.EqvGen.rel _ _ seam

end Unfoldings.MetricGluing
