module

public import Unfoldings.Metric.BankStackGraft
public import Mathlib.Data.List.Nodup

/-! Original bank-stack addresses separate all consecutive seam endpoints combinatorially. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)

/-- An original attachment, piece tag, bank side, and parameter, before identifying banks. -/
abbrev BankStackAddress := Σ e, Option G × Bool × Parameter e

/-- The literal address of the left bank of a consecutive stack seam. -/
def bankStackLeftAddress (slot : BankStackSlot stack) (t : Parameter slot.1) :
    BankStackAddress (G := G) (Parameter := Parameter) :=
  if initial : slot.2.val = 0 then ⟨slot.1, none, false, t⟩ else
    ⟨slot.1, some ((stack slot.1)[slot.2.val - 1]'(by have bound := slot.2.isLt; omega)), true, t⟩

/-- The literal right-bank address includes the original final bank of an empty stack. -/
def bankStackRightAddress (slot : BankStackSlot stack) (t : Parameter slot.1) :
    BankStackAddress (G := G) (Parameter := Parameter) :=
  if before : slot.2.val < (stack slot.1).length then
    ⟨slot.1, some ((stack slot.1)[slot.2.val]'before), false, t⟩
  else ⟨slot.1, none, true, t⟩

/-- A repeated source is the only possible combinatorial ambiguity between left addresses. -/
theorem bankStackLeftAddress_injective (nodup : ∀ e, (stack e).Nodup) : Function.Injective
    (fun p : Σ slot : BankStackSlot stack, Parameter slot.1 =>
      bankStackLeftAddress stack p.1 p.2) := by
  rintro ⟨⟨e, i⟩, t⟩ ⟨⟨f, j⟩, s⟩ equal
  have bank_eq : e = f := by
    have named := congrArg Sigma.fst equal
    simp only [bankStackLeftAddress, apply_dite] at named
    split_ifs at named <;> exact named
  subst f
  dsimp only at equal
  unfold bankStackLeftAddress at equal
  split at equal <;> split at equal
  · rename_i first last
    have indices : i = j := Fin.ext (first.trans last.symm)
    subst j
    have parameter : t = s := congrArg (fun p : Option G × Bool × Parameter e => p.2.2)
      (eq_of_heq (Sigma.mk.inj equal).2)
    subst s
    rfl
  · have impossible := (Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)).1
    cases impossible
  · have impossible := (Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)).1
    cases impossible
  · rename_i first last
    have named := Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)
    have indices_value := (nodup e).getElem_inj_iff.mp (Option.some.inj named.1)
    dsimp only at first last indices_value
    have indices : i = j := Fin.ext (by omega)
    subst j
    have parameter : t = s := (Prod.mk.inj named.2).2
    subst s
    rfl

/-- Right addresses likewise retain the original seam slot and parameter. -/
theorem bankStackRightAddress_injective (nodup : ∀ e, (stack e).Nodup) : Function.Injective
    (fun p : Σ slot : BankStackSlot stack, Parameter slot.1 =>
      bankStackRightAddress stack p.1 p.2) := by
  rintro ⟨⟨e, i⟩, t⟩ ⟨⟨f, j⟩, s⟩ equal
  have bank_eq : e = f := by
    have named := congrArg Sigma.fst equal
    simp only [bankStackRightAddress, apply_dite] at named
    split_ifs at named <;> exact named
  subst f
  dsimp only at equal
  unfold bankStackRightAddress at equal
  split at equal <;> split at equal
  · have named := Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)
    have indices : i = j := Fin.ext
      ((nodup e).getElem_inj_iff.mp (Option.some.inj named.1))
    subst j
    have parameter : t = s := (Prod.mk.inj named.2).2
    subst s
    rfl
  · have impossible := (Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)).1
    cases impossible
  · have impossible := (Prod.mk.inj (eq_of_heq (Sigma.mk.inj equal).2)).1
    cases impossible
  · rename_i first last
    dsimp only at first last
    have indices : i = j := Fin.ext (by have a := i.isLt; have b := j.isLt; omega)
    subst j
    have parameter : t = s := congrArg (fun p : Option G × Bool × Parameter e => p.2.2)
      (eq_of_heq (Sigma.mk.inj equal).2)
    subst s
    rfl

/-- A left address is never a right address, even for distinct original attachments. -/
theorem bankStackLeftAddress_ne_rightAddress (slot other : BankStackSlot stack)
    (t : Parameter slot.1) (s : Parameter other.1) :
    bankStackLeftAddress stack slot t ≠ bankStackRightAddress stack other s := by
  intro equal
  unfold bankStackLeftAddress bankStackRightAddress at equal
  split_ifs at equal
  all_goals
    have flags := congrArg (fun p : BankStackAddress (G := G) (Parameter := Parameter) =>
      match p.2.1 with
      | none => !p.2.2.1
      | some _ => p.2.2.1) equal
    cases flags

end Unfoldings.MetricGluing
