module

public import Unfoldings.Metric.BankStackAdjacentGaps

/-! The names on both ends of an arbitrary interior slot of an ordered bank stack. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)

theorem bankStack_internal_slot_names (e : Edge) (i : Fin ((stack e).length + 1))
    (t : Parameter e) (positive : 0 < i.val) (before_end : i.val < (stack e).length) :
    ∃ (g h : G) (before after : List G),
      stack e = before ++ g :: h :: after ∧
      bankStackEndpointAddress stack false ⟨e, i⟩ t = ⟨e, some g, true, t⟩ ∧
      bankStackEndpointAddress stack true ⟨e, i⟩ t = ⟨e, some h, false, t⟩ := by
  let l := stack e
  have prior : i.val - 1 < l.length := by exact (Nat.sub_le _ _).trans_lt before_end
  let g := l[i.val - 1]
  let h := l[i.val]
  have rank : i.val - 1 + 1 = i.val := by omega
  have drop_first : l.drop (i.val - 1) = g :: l.drop i.val := by
    have ht := List.drop_eq_getElem_cons prior
    rw [rank] at ht
    exact ht
  have shape : l = l.take (i.val - 1) ++ g :: h :: l.drop (i.val + 1) := by
    rw [← List.drop_eq_getElem_cons before_end, ← drop_first, List.take_append_drop]
  refine ⟨g, h, l.take (i.val - 1), l.drop (i.val + 1), shape, ?_, ?_⟩
  · change bankStackLeftAddress stack ⟨e, i⟩ t = _
    unfold bankStackLeftAddress
    rw [dite_eq_right (show i.val ≠ 0 from positive.ne')]
  · change bankStackRightAddress stack ⟨e, i⟩ t = _
    unfold bankStackRightAddress
    rw [dite_eq_left (show i.val < (stack e).length from before_end)]

variable (X : Option G → Type*) (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- Equal complete bank addresses pick the same tagged point. -/
theorem bankStackEndpoint_eq_of_same_address (a b : Bool)
    (p q : Σ slot : BankStackSlot stack, Parameter slot.1)
    (equal : bankStackEndpointAddress stack a p.1 p.2 = bankStackEndpointAddress stack b q.1 q.2) :
    bankStackEndpoint stack X base gap a p.1 p.2 = bankStackEndpoint stack X base gap b q.1 q.2 := by
  let interpretation (addr : BankStackAddress (G := G) (Parameter := Parameter)) :=
    ∀ valid : BankStackAddressValid stack addr, bankStackAddressPoint stack X base gap addr valid =
      bankStackEndpoint stack X base gap b q.1 q.2
  have known : interpretation (bankStackEndpointAddress stack b q.1 q.2) := fun _ =>
    bankStackAddressPoint_endpoint stack X base gap b q.1 q.2
  exact (bankStackAddressPoint_endpoint stack X base gap a p.1 p.2).symm.trans
    ((equal.symm ▸ known : interpretation (bankStackEndpointAddress stack a p.1 p.2)) _)

end Unfoldings.MetricGluing
