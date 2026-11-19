module

public import Unfoldings.Metric.BankStackGraft

/-! Original bank labels pass through every consecutive attachment of a gap stack. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge L : Type*} {Parameter : Edge → Type*} (X : Option G → Type*)
  (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  (label : Total X → L) (bankLabel : ∀ e, Parameter e → L)
  (base_label : ∀ e side t, label ⟨none, base e side t⟩ = bankLabel e t)
  (gap_label : ∀ e g member side t, label ⟨some g, gap e g member side t⟩ = bankLabel e t)

include base_label gap_label

/-- Every selected left curve keeps the original bank label, including empty stacks. -/
theorem bankStackLeft_label (slot : BankStackSlot stack) (t : Parameter slot.1) :
    label (bankStackLeft X stack base gap slot t) = bankLabel slot.1 t := by
  unfold bankStackLeft
  split
  · exact base_label _ false t
  · exact gap_label _ _ _ true t

/-- Every selected right curve keeps the same original label through the last bank. -/
theorem bankStackRight_label (slot : BankStackSlot stack) (t : Parameter slot.1) :
    label (bankStackRight X stack base gap slot t) = bankLabel slot.1 t := by
  unfold bankStackRight
  split
  · exact gap_label _ _ _ false t
  · exact base_label _ true t

/-- All actual consecutive stack attachments preserve the original physical bank labels. -/
theorem bankStackSeams_label (a b : Total X)
    (joined : bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap) a b) :
    label a = label b := by
  obtain ⟨slot, t, rfl, rfl⟩ := joined
  exact (bankStackLeft_label X stack base gap label bankLabel base_label gap_label slot t).trans
    (bankStackRight_label X stack base gap label bankLabel base_label gap_label slot t).symm

end Unfoldings.MetricGluing
