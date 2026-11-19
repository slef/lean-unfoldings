module

public import Unfoldings.Metric.BankStackGraft

/-! A singleton stack has exactly the two literal seams of its original gap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {Edge G : Type*} {Parameter : Edge → Type*} (X : Option G → Type*)
  (stack : Edge → List G) (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  (e : Edge) (g : G) (one : stack e = [g]) (t : Parameter e)

private theorem singleton_mark {g h : G} (same : h = g) (left : h ∈ stack e)
    (right : g ∈ stack e) (side : Bool) :
    (⟨some h, gap e h left side t⟩ : Total X) = ⟨some g, gap e g right side t⟩ := by
  subst h
  rfl

private theorem getElem_singleton_of_eq {l : List G} {g : G} (one : l = [g])
    (i : ℕ) (bound : i < l.length) : l[i] = g := by
  subst l
  exact List.mem_singleton.mp (List.getElem_mem bound)

include one in
/-- The first stack slot is from the exit bank to the first side of the gap. -/
theorem bankStack_singleton_first (member : g ∈ stack e) :
    bankStackLeft X stack base gap ⟨e, 0⟩ t = ⟨none, base e false t⟩ ∧
    bankStackRight X stack base gap ⟨e, 0⟩ t = ⟨some g, gap e g member false t⟩ := by
  refine ⟨bankStackLeft_first X stack base gap e t, ?_⟩
  let i : Fin (stack e).length := ⟨0, by rw [one]; exact Nat.zero_lt_succ _⟩
  have label : (stack e)[i.val] = g := getElem_singleton_of_eq one i.val i.isLt
  exact (bankStackRight_at X stack base gap e i t).trans
    (singleton_mark X stack gap e t label _ member false)

include one in
/-- The last stack slot is from the other side of the gap to the entrance bank. -/
theorem bankStack_singleton_last (member : g ∈ stack e) :
    bankStackLeft X stack base gap ⟨e, Fin.last (stack e).length⟩ t =
      ⟨some g, gap e g member true t⟩ ∧
    bankStackRight X stack base gap ⟨e, Fin.last (stack e).length⟩ t =
      ⟨none, base e true t⟩ := by
  refine ⟨?_, bankStackRight_last X stack base gap e t⟩
  let i : Fin (stack e).length := ⟨0, by rw [one]; exact Nat.zero_lt_succ _⟩
  have last : i.succ = Fin.last (stack e).length := by
    apply Fin.ext
    change 1 = (stack e).length
    rw [one]
    rfl
  have label : (stack e)[i.val] = g := getElem_singleton_of_eq one i.val i.isLt
  rw [← last, bankStackLeft_after]
  exact singleton_mark X stack gap e t label _ member true

include one in
/-- There is no intermediate bank slot between the two sides of a singleton stack. -/
theorem bankStack_singleton_slot_cases (i : Fin ((stack e).length + 1)) :
    i = 0 ∨ i = Fin.last (stack e).length := by
  have length : (stack e).length = 1 := by rw [one]; rfl
  have bound := i.isLt
  rcases Nat.eq_zero_or_pos i.val with zero | positive
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Fin.ext (by rw [Fin.val_last]; omega))

end Unfoldings.MetricGluing
