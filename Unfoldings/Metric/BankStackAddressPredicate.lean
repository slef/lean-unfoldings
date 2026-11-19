module

public import Unfoldings.Metric.BankStackLocalClasses

/-! Recover the piece and bank side when a join admits several legitimate times. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)
  (X : Option G → Type*)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- A predicate on attachment parameters covers all mark equalities at the chosen time. -/
structure BankStackMarkParametersAt (e : Edge) (t : Parameter e)
    (admissible : (Σ b, Parameter b) → Prop) : Prop where
  base_eq : ∀ side f other_side s, base f other_side s = base e side t →
    other_side = side ∧ admissible ⟨f, s⟩
  gap_eq : ∀ g member side f other_member other_side s,
    gap f g other_member other_side s = gap e g member side t →
      other_side = side ∧ admissible ⟨f, s⟩

/-- All equal marks keep their piece and side, with one of the admissible parameters. -/
theorem bankStackAddress_tags_of_point_eq (e : Edge) (t : Parameter e)
    {admissible : (Σ b, Parameter b) → Prop}
    (covered : BankStackMarkParametersAt stack X base gap e t admissible)
    (piece : Option G) (side : Bool)
    (valid : BankStackAddressValid stack ⟨e, piece, side, t⟩)
    (other : BankStackAddress (G := G) (Parameter := Parameter))
    (other_valid : BankStackAddressValid stack other)
    (equal : bankStackAddressPoint stack X base gap other other_valid =
      bankStackAddressPoint stack X base gap ⟨e, piece, side, t⟩ valid) :
    other.2.1 = piece ∧ other.2.2.1 = side ∧ admissible ⟨other.1, other.2.2.2⟩ := by
  obtain ⟨f, other_piece, other_side, s⟩ := other
  cases piece with
  | none =>
    cases other_piece with
    | none =>
      exact ⟨rfl, covered.base_eq side f other_side s (eq_of_heq (Sigma.mk.inj equal).2)⟩
    | some h =>
      cases congrArg Sigma.fst equal
  | some g =>
    cases other_piece with
    | none =>
      cases congrArg Sigma.fst equal
    | some h =>
      have tags : h = g := Option.some.inj (congrArg Sigma.fst equal)
      subst h
      exact ⟨rfl, covered.gap_eq g valid side f other_valid other_side s
        (eq_of_heq (Sigma.mk.inj equal).2)⟩

/-- A literal endpoint address keeps the attachment and time used to construct it. -/
theorem bankStackEndpointAddress_parameter (side : Bool) (slot : BankStackSlot stack)
    (t : Parameter slot.1) :
    let a := bankStackEndpointAddress stack side slot t
    (⟨a.1, a.2.2.2⟩ : Σ b, Parameter b) = ⟨slot.1, t⟩ := by
  let P (a : BankStackAddress (G := G) (Parameter := Parameter)) :=
    (⟨a.1, a.2.2.2⟩ : Σ b, Parameter b) = ⟨slot.1, t⟩
  cases side
  · change P (bankStackLeftAddress stack slot t)
    unfold bankStackLeftAddress
    split <;> rfl
  · change P (bankStackRightAddress stack slot t)
    unfold bankStackRightAddress
    split <;> rfl

/-- Comparison with a named endpoint recovers its literal piece and bank side. -/
theorem bankStackEndpoint_tags_of_point_eq (side other_side : Bool)
    (slot other : BankStackSlot stack) (t : Parameter slot.1) (s : Parameter other.1)
    {admissible : (Σ b, Parameter b) → Prop}
    (covered : BankStackMarkParametersAt stack X base gap slot.1 t admissible)
    (equal : bankStackEndpoint stack X base gap other_side other s =
      bankStackEndpoint stack X base gap side slot t) :
    let a := bankStackEndpointAddress stack side slot t
    let b := bankStackEndpointAddress stack other_side other s
    b.2.1 = a.2.1 ∧ b.2.2.1 = a.2.2.1 ∧ admissible ⟨other.1, s⟩ := by
  let a := bankStackEndpointAddress stack side slot t
  let b := bankStackEndpointAddress stack other_side other s
  have at_a : BankStackMarkParametersAt stack X base gap a.1 a.2.2.2 admissible := by
    let P (x : Σ e, Parameter e) := BankStackMarkParametersAt stack X base gap x.1 x.2 admissible
    change P ⟨a.1, a.2.2.2⟩
    rw [show (⟨a.1, a.2.2.2⟩ : Σ b, Parameter b) = ⟨slot.1, t⟩ from
      bankStackEndpointAddress_parameter stack side slot t]
    exact covered
  have points := (bankStackAddressPoint_endpoint stack X base gap other_side other s).trans
    (equal.trans (bankStackAddressPoint_endpoint stack X base gap side slot t).symm)
  have tags := bankStackAddress_tags_of_point_eq stack X base gap _ _ at_a a.2.1 a.2.2.1
    (bankStackEndpointAddress_valid stack side slot t) b
    (bankStackEndpointAddress_valid stack other_side other s) points
  exact ⟨tags.1, tags.2.1, bankStackEndpointAddress_parameter stack other_side other s ▸ tags.2.2⟩

end Unfoldings.MetricGluing
