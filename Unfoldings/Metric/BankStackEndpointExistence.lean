module

public import Unfoldings.Metric.BankStackLocalClasses

/-! Every valid bank mark occurs at one original stack endpoint. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)

/-- The original marked addresses are precisely the addresses of the actual stack endpoints. -/
theorem exists_bankStackEndpointAddress_eq
    (a : BankStackAddress (G := G) (Parameter := Parameter))
    (valid : BankStackAddressValid stack a) :
    ∃ (side : Bool) (slot : BankStackSlot stack) (t : Parameter slot.1),
      bankStackEndpointAddress stack side slot t = a := by
  obtain ⟨e, piece, flag, t⟩ := a
  cases piece with
  | none =>
    cases flag
    · exact ⟨false, ⟨e, 0⟩, t, by simp [bankStackEndpointAddress, bankStackLeftAddress]⟩
    · exact ⟨true, ⟨e, Fin.last (stack e).length⟩, t,
        by simp [bankStackEndpointAddress, bankStackRightAddress]⟩
  | some g =>
    change g ∈ stack e at valid
    obtain ⟨i, name⟩ := List.get_of_mem valid
    cases flag
    · have bound : i.val < (stack e).length := i.isLt
      refine ⟨true, ⟨e, i.castSucc⟩, t, ?_⟩
      simpa only [bankStackEndpointAddress, ite_true, bankStackRightAddress, dite_eq_left bound, List.get_eq_getElem, Fin.val_castSucc]
        using congrArg (fun h =>
          (⟨e, some h, false, t⟩ : BankStackAddress (G := G) (Parameter := Parameter))) name
    · have nonzero : i.val + 1 ≠ 0 := Nat.succ_ne_zero i.val
      refine ⟨false, ⟨e, i.succ⟩, t, ?_⟩
      simpa only [bankStackEndpointAddress, Bool.false_eq_true, ite_false, bankStackLeftAddress,
        dite_eq_right nonzero, List.get_eq_getElem, Fin.val_succ, Nat.add_sub_cancel]
        using congrArg (fun h =>
          (⟨e, some h, true, t⟩ : BankStackAddress (G := G) (Parameter := Parameter))) name

/-- The newest gap meets the exit bank at the first stack slot. -/
theorem bankStack_first_gap_addresses (e : Edge) (t : Parameter e)
    (g : G) (tail : List G) (shape : stack e = g :: tail) :
    bankStackEndpointAddress stack false ⟨e, 0⟩ t = ⟨e, none, false, t⟩ ∧
    bankStackEndpointAddress stack true ⟨e, 0⟩ t = ⟨e, some g, false, t⟩ := by
  constructor
  · simp [bankStackEndpointAddress, bankStackLeftAddress]
  · simp [bankStackEndpointAddress, bankStackRightAddress, shape]

private theorem getElem_last_of_append {l before : List G} {g : G}
    (shape : l = before ++ [g]) (bound : l.length - 1 < l.length) :
    l[l.length - 1] = g := by
  subst l
  simp [List.getElem_append_right]

/-- The oldest gap meets the entrance bank at the final stack slot. -/
theorem bankStack_last_gap_addresses (e : Edge) (t : Parameter e)
    (g : G) (before : List G) (shape : stack e = before ++ [g]) :
    let slot : BankStackSlot stack := ⟨e, Fin.last (stack e).length⟩
    bankStackEndpointAddress stack false slot t = ⟨e, some g, true, t⟩ ∧
    bankStackEndpointAddress stack true slot t = ⟨e, none, true, t⟩ := by
  have positive : 0 < (stack e).length := by simp [shape]
  constructor
  · simp only [bankStackEndpointAddress, Bool.false_eq_true, ite_false, bankStackLeftAddress,
      Fin.val_last, dite_eq_right positive.ne']
    exact congrArg (fun h =>
      (⟨e, some h, true, t⟩ : BankStackAddress (G := G) (Parameter := Parameter)))
      (getElem_last_of_append shape (by omega))
  · simp [bankStackEndpointAddress, bankStackRightAddress]

/-- An attachment with no gaps restores its two literal original addresses. -/
theorem bankStack_empty_addresses (e : Edge) (t : Parameter e) (empty : stack e = []) :
    bankStackEndpointAddress stack false ⟨e, 0⟩ t = ⟨e, none, false, t⟩ ∧
    bankStackEndpointAddress stack true ⟨e, 0⟩ t = ⟨e, none, true, t⟩ := by
  simp [bankStackEndpointAddress, bankStackLeftAddress, bankStackRightAddress, empty]

variable (X : Option G → Type*) (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- A literal base endpoint address evaluates to the original roof mark. -/
theorem bankStackEndpoint_eq_of_base_address
    (side : Bool) (p : Σ slot : BankStackSlot stack, Parameter slot.1)
    (e : Edge) (flag : Bool) (t : Parameter e)
    (named : bankStackEndpointAddress stack side p.1 p.2 = ⟨e, none, flag, t⟩) :
    bankStackEndpoint stack X base gap side p.1 p.2 = ⟨none, base e flag t⟩ := by
  let P (a : BankStackAddress (G := G) (Parameter := Parameter)) :=
    ∀ valid : BankStackAddressValid stack a,
      bankStackEndpoint stack X base gap side p.1 p.2 =
        bankStackAddressPoint stack X base gap a valid
  have exact_address : P (bankStackEndpointAddress stack side p.1 p.2) := fun _ =>
    (bankStackAddressPoint_endpoint stack X base gap side p.1 p.2).symm
  exact (named ▸ exact_address) trivial

end Unfoldings.MetricGluing
