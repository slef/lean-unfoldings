module

public import Unfoldings.Metric.Excision
public import Unfoldings.Metric.ClosedSeamOperations
public import Unfoldings.Metric.FiniteLabelClasses

/-! Conserved labels exclude unwanted seam families from a whole local metric ball. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I L : Type*} {E : I → Type*} [∀ i, MetricSpace (E i)]
  (S T : ClosedSeams E)

/-- Restore the second seam family, retaining the first family's exact original domains. -/
theorem relation_included_sum (a b : Total E) (joined : S.relation a b) :
    (S.sum T).relation a b := (S.sum_relation T a b).mpr (Or.inl joined)

/-- If the added seams have conserved labels absent at the center, removing all of
those seams leaves a sufficiently small whole intrinsic ball unchanged. -/
theorem exists_forgetChart_sum_of_label
    (label : Total E → L)
    (compatible : ∀ a b, (S.sum T).relation a b → label a = label b)
    (selected : L → Prop)
    (added : ∀ a b, T.relation a b → selected (label a))
    (a : Total E) (finite : ∀ i, (classIn E (S.sum T).relation a i).Finite)
    (outside : ¬ selected (label a)) :
    Nonempty (ForgetChart E (S.relation_included_sum T) a) := by
  apply (S.sum T).exists_forgetChart a finite S.relation (S.relation_included_sum T)
  intro seam incident x
  cases seam with
  | inl s => exact ⟨s, x, rfl, rfl⟩
  | inr s =>
    obtain ⟨p, related, t, equal⟩ := incident
    have same : label a = label ⟨T.left s, T.toLeft s t⟩ :=
      (label_eq_of_eqvGen (S.sum T).relation label compatible related).trans
        (congrArg (fun q => label ⟨T.left s, q⟩) equal.symm)
    have forbidden := added _ _ ⟨s, t, rfl, rfl⟩
    exact (outside (same.symm ▸ forbidden)).elim

end Unfoldings.MetricGluing.ClosedSeams
