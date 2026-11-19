module

public import Unfoldings.Metric.BankStackAddresses

/-! Recover original marked-bank addresses from equal intrinsic piece points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)
  (X : Option G → Type*)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- A gap address must name a gap actually occurring on the original attachment. -/
def BankStackAddressValid (a : BankStackAddress (G := G) (Parameter := Parameter)) : Prop :=
  match a.2.1 with
  | none => True
  | some g => g ∈ stack a.1

/-- Interpret a valid original bank address in its original intrinsic metric piece. -/
def bankStackAddressPoint (a : BankStackAddress (G := G) (Parameter := Parameter))
    (valid : BankStackAddressValid stack a) : Total X :=
  match a with
  | ⟨e, none, side, t⟩ => ⟨none, base e side t⟩
  | ⟨e, some g, side, t⟩ => ⟨some g, gap e g valid side t⟩

/-- Intrinsic marks at one original parameter recover attachment, side and parameter.
No metric quotient or local flatness conclusion is included in these hypotheses. -/
structure BankStackUniqueMarksAt (e : Edge) (t : Parameter e) : Prop where
  base_eq : ∀ side f other_side s, base f other_side s = base e side t →
    other_side = side ∧ (⟨f, s⟩ : Σ b, Parameter b) = ⟨e, t⟩
  gap_eq : ∀ g member side f other_member other_side s,
    gap f g other_member other_side s = gap e g member side t →
      other_side = side ∧ (⟨f, s⟩ : Σ b, Parameter b) = ⟨e, t⟩

/-- Individual original mark uniqueness recovers the full address of any equal piece point. -/
theorem bankStackAddress_eq_of_point_eq (e : Edge) (t : Parameter e)
    (unique : BankStackUniqueMarksAt stack X base gap e t) (piece : Option G) (side : Bool)
    (valid : BankStackAddressValid stack ⟨e, piece, side, t⟩)
    (other : BankStackAddress (G := G) (Parameter := Parameter))
    (other_valid : BankStackAddressValid stack other)
    (equal : bankStackAddressPoint stack X base gap other other_valid =
      bankStackAddressPoint stack X base gap ⟨e, piece, side, t⟩ valid) :
    other = ⟨e, piece, side, t⟩ := by
  obtain ⟨f, other_piece, other_side, s⟩ := other
  cases piece with
  | none =>
    cases other_piece with
    | none =>
      have named := unique.base_eq side f other_side s
        (eq_of_heq (Sigma.mk.inj equal).2)
      have flags := named.1
      subst other_side
      exact congrArg (fun p : Σ b, Parameter b =>
        (⟨p.1, none, side, p.2⟩ : BankStackAddress (G := G) (Parameter := Parameter))) named.2
    | some h =>
      have tags := congrArg Sigma.fst equal
      cases tags
  | some g =>
    cases other_piece with
    | none =>
      have tags := congrArg Sigma.fst equal
      cases tags
    | some h =>
      have tags : h = g := Option.some.inj (congrArg Sigma.fst equal)
      subst h
      have named := unique.gap_eq g valid side f other_valid other_side s
        (eq_of_heq (Sigma.mk.inj equal).2)
      have flags := named.1
      subst other_side
      exact congrArg (fun p : Σ b, Parameter b =>
        (⟨p.1, some g, side, p.2⟩ : BankStackAddress (G := G) (Parameter := Parameter))) named.2

/-- Every actual left-bank address names a gap in its original stack. -/
theorem bankStackLeftAddress_valid (slot : BankStackSlot stack) (t : Parameter slot.1) :
    BankStackAddressValid stack (bankStackLeftAddress stack slot t) := by
  unfold bankStackLeftAddress
  split
  · trivial
  · exact List.getElem_mem _

/-- Every actual right-bank address is valid, including the final original roof bank. -/
theorem bankStackRightAddress_valid (slot : BankStackSlot stack) (t : Parameter slot.1) :
    BankStackAddressValid stack (bankStackRightAddress stack slot t) := by
  unfold bankStackRightAddress
  split
  · exact List.getElem_mem _
  · trivial

/-- Interpreting a left address gives the literal original left seam endpoint. -/
theorem bankStackAddressPoint_left (slot : BankStackSlot stack) (t : Parameter slot.1) :
    bankStackAddressPoint stack X base gap (bankStackLeftAddress stack slot t)
      (bankStackLeftAddress_valid stack slot t) = bankStackLeft X stack base gap slot t := by
  unfold bankStackLeftAddress bankStackLeft
  split <;> rfl

/-- Interpreting a right address gives the literal original right seam endpoint. -/
theorem bankStackAddressPoint_right (slot : BankStackSlot stack) (t : Parameter slot.1) :
    bankStackAddressPoint stack X base gap (bankStackRightAddress stack slot t)
      (bankStackRightAddress_valid stack slot t) = bankStackRight X stack base gap slot t := by
  unfold bankStackRightAddress bankStackRight
  split <;> rfl

end Unfoldings.MetricGluing
