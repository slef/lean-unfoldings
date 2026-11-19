module

public import Unfoldings.Metric.BankStackLocalClasses
public import Unfoldings.Metric.BankStackIncidentSlots

/-! A consecutive pair of inserted gaps has the same seam throughout a repeated block. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)

private theorem adjacent_marks {l : List G} {before after : List G} {g h : G}
    (shape : l = before ++ g :: h :: after) :
    ∃ (i : Fin (l.length + 1))
      (bound : i.val < l.length) (nonzero : i.val ≠ 0),
      l[i.val - 1]'(by omega) = g ∧ l[i.val] = h := by
  subst l
  let j := before.length
  have size : (before ++ g :: h :: after).length = j + (after.length + 2) := by
    simp only [List.length_append, List.length_cons, j]
  let i : Fin ((before ++ g :: h :: after).length + 1) :=
    ⟨j + 1, by omega⟩
  have before_end : i.val < (before ++ g :: h :: after).length := by
    change j + 1 < _
    omega
  have nonzero : i.val ≠ 0 := by
    change j + 1 ≠ 0
    omega
  refine ⟨i, before_end, nonzero, ?_, ?_⟩
  · have p : i.val - 1 = before.length := by simp [i, j]
    simp only [p]
    simp only [List.getElem_append_right (le_rfl : before.length ≤ before.length),
      Nat.sub_self, List.getElem_cons_zero]
  · have p : i.val - before.length = 1 := by simp [i, j]
    simp only [List.getElem_append_right (by omega : before.length ≤ i.val), p,
      List.getElem_cons_succ, List.getElem_cons_zero]

/-- A consecutive pair in a literal list block is attached through its original two marks. -/
theorem bankStack_exists_adjacent_gap_slot (e : Edge) (t : Parameter e)
    {g h : G} {before after : List G} (shape : stack e = before ++ g :: h :: after) :
    ∃ i : Fin ((stack e).length + 1),
      bankStackEndpointAddress stack false ⟨e, i⟩ t = ⟨e, some g, true, t⟩ ∧
      bankStackEndpointAddress stack true ⟨e, i⟩ t = ⟨e, some h, false, t⟩ := by
  obtain ⟨i, bound, nonzero, left, right⟩ := adjacent_marks shape
  let slot : BankStackSlot stack := ⟨e, i⟩
  -- Give the time argument its original dependent type.
  let time : Parameter slot.1 := t
  refine ⟨i, ?_, ?_⟩
  · change bankStackLeftAddress stack slot time = _
    unfold bankStackLeftAddress
    rw [dite_eq_right (show slot.2.val ≠ 0 from nonzero)]
    exact congrArg (fun a => (⟨e, some a, true, t⟩ : BankStackAddress (G := G) (Parameter := Parameter))) left
  · change bankStackRightAddress stack slot time = _
    unfold bankStackRightAddress
    rw [dite_eq_left (show slot.2.val < (stack slot.1).length from bound)]
    exact congrArg (fun a => (⟨e, some a, false, t⟩ : BankStackAddress (G := G) (Parameter := Parameter))) right

/-- A named endpoint on a fixed slot retains its piece and side at every parameter. -/
theorem bankStackEndpointAddress_at_time
    (side : Bool) (slot : BankStackSlot stack) (t u : Parameter slot.1)
    (g : G) (flag : Bool)
    (named : bankStackEndpointAddress stack side slot t = ⟨slot.1, some g, flag, t⟩) :
    bankStackEndpointAddress stack side slot u = ⟨slot.1, some g, flag, u⟩ := by
  cases side
  · change bankStackLeftAddress stack slot t = _ at named
    change bankStackLeftAddress stack slot u = _
    unfold bankStackLeftAddress at named ⊢
    split at named
    · cases congrArg (fun p : BankStackAddress (G := G) (Parameter := Parameter) => p.2.1) named
    · rename_i not_first
      rw [dite_eq_right not_first]
      exact congrArg (fun p : BankStackAddress (G := G) (Parameter := Parameter) =>
        (⟨slot.1, p.2.1, p.2.2.1, u⟩ : BankStackAddress (G := G) (Parameter := Parameter))) named
  · change bankStackRightAddress stack slot t = _ at named
    change bankStackRightAddress stack slot u = _
    unfold bankStackRightAddress at named ⊢
    split at named
    · rename_i before_end
      rw [dite_eq_left before_end]
      exact congrArg (fun p : BankStackAddress (G := G) (Parameter := Parameter) =>
        (⟨slot.1, p.2.1, p.2.2.1, u⟩ : BankStackAddress (G := G) (Parameter := Parameter))) named
    · cases congrArg (fun p : BankStackAddress (G := G) (Parameter := Parameter) => p.2.1) named

variable (X : Option G → Type*) (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "End" => bankStackEndpoint stack X base gap
local notation "L" => bankStackLeft X stack base gap
local notation "Rgt" => bankStackRight X stack base gap
local notation "Banks" => bankSeams L Rgt
local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))

/-- A parameter on either selected slot is obtained from its given coordinate. -/
theorem bankStack_exists_named_time {U : Type*}
    (first second : BankStackSlot stack)
    (h₀ : U ≃ Parameter first.1) (h₁ : U ≃ Parameter second.1)
    (x : Time) (fits : x.1 = first ∨ x.1 = second) :
    ∃ (side : Bool) (t : U),
      x = if side then (⟨second, h₁ t⟩ : Time) else ⟨first, h₀ t⟩ := by
  obtain ⟨s, u⟩ := x
  rcases fits with named | named
  · change s = first at named
    subst s
    obtain ⟨t, fits⟩ := h₀.surjective u
    exact ⟨false, t, congrArg (Sigma.mk first) fits.symm⟩
  · change s = second at named
    subst s
    obtain ⟨t, fits⟩ := h₁.surjective u
    exact ⟨true, t, congrArg (Sigma.mk second) fits.symm⟩

/-- A literal gap endpoint address evaluates to the original intrinsic bank mark. -/
theorem bankStackEndpoint_eq_of_gap_address
    (side : Bool) (p : Time) (e : Edge) (g : G) (member : g ∈ stack e)
    (flag : Bool) (t : Parameter e)
    (named : bankStackEndpointAddress stack side p.1 p.2 = ⟨e, some g, flag, t⟩) :
    End side p.1 p.2 = ⟨some g, gap e g member flag t⟩ := by
  let P (a : BankStackAddress (G := G) (Parameter := Parameter)) :=
    ∀ valid : BankStackAddressValid stack a,
      End side p.1 p.2 = bankStackAddressPoint stack X base gap a valid
  have exact_address : P (bankStackEndpointAddress stack side p.1 p.2) := fun _ =>
    (bankStackAddressPoint_endpoint stack X base gap side p.1 p.2).symm
  exact (named ▸ exact_address) member

/-- If the two names of one attachment pair account for all endpoint addresses of
both pieces, they account for the exact whole seam class as well. -/
theorem bankStack_eqvGen_pair_of_two_slot_times
    (first second : Time)
    (same : ∀ side, End side first.1 first.2 = End side second.1 second.2)
    (recover : ∀ side other (where_ : Time),
      End other where_.1 where_.2 = End side first.1 first.2 →
      other = side ∧ (where_ = first ∨ where_ = second))
    (x : Total X) :
    Relation.EqvGen Banks (L first.1 first.2) x ↔
      x = L first.1 first.2 ∨ x = Rgt first.1 first.2 := by
  let is_pair (z : Total X) := z = L first.1 first.2 ∨ z = Rgt first.1 first.2
  have at_slot (other : Bool) (w : Time) :
      is_pair (End other w.1 w.2) ↔ w = first ∨ w = second := by
    constructor
    · rintro (h | h)
      · exact (recover false other w h).2
      · exact (recover true other w h).2
    · rintro (rfl | rfl)
      · cases other
        · exact Or.inl rfl
        · exact Or.inr rfl
      · cases other
        · exact Or.inl (same false).symm
        · exact Or.inr (same true).symm
  have closed : ∀ u v, Banks u v → (is_pair u ↔ is_pair v) := by
    rintro _ _ ⟨slot, t, rfl, rfl⟩
    exact (at_slot false ⟨slot, t⟩).trans (at_slot true ⟨slot, t⟩).symm
  have invariant {u v : Total X} (path : Relation.EqvGen Banks u v) :
      is_pair u ↔ is_pair v := by
    induction path with
    | rel u v edge => exact closed u v edge
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hl hr => exact hl.trans hr
  constructor
  · intro path
    exact (invariant path).mp (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ ⟨first.1, first.2, rfl, rfl⟩

variable [∀ i, EMetricSpace (X i)] [Finite Edge] [∀ e, TopologicalSpace (Parameter e)]

/-- A finite exact pair class with two genuine names has only those adjacent slots
in a sufficiently small whole graft ball. -/
theorem bankStack_exists_near_two_slots (first second : Time)
    (class_eq : ∀ z, Relation.EqvGen Banks (L first.1 first.2) z →
      z = L first.1 first.2 ∨ z = Rgt first.1 first.2)
    (recover : ∀ side other (p : Time),
      End other p.1 p.2 = End side first.1 first.2 →
        other = side ∧ (p = first ∨ p = second))
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (positive : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (point X Banks (L first.1 first.2)) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks (L first.1 first.2) ⟨b.1, c⟩ ∧
        edist c b.2 < ENNReal.ofReal r) :
    ∃ r > 0, ∀ (slot : BankStackSlot stack) (t : Parameter slot.1),
      edist (point X Banks (L first.1 first.2)) (point X Banks (L slot t)) < ENNReal.ofReal r →
      slot = first.1 ∨ slot = second.1 := by
  have finite (i : Option G) :
      {q : X i | Relation.EqvGen Banks (L first.1 first.2) ⟨i, q⟩}.Finite := by
    have candidates := (Set.finite_singleton (L first.1 first.2)).union
      (Set.finite_singleton (Rgt first.1 first.2))
    have injective : Function.Injective (fun q : X i => (⟨i, q⟩ : Total X)) :=
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
    exact (candidates.preimage injective.injOn).subset fun _ h => class_eq _ h
  obtain ⟨r, rpos, slots⟩ := exists_bankStack_incident_slot_radius X stack base gap
    (L first.1 first.2) finite base_closed gap_closed positive cover
  refine ⟨r, rpos, ?_⟩
  intro slot t near
  obtain ⟨u, related, _⟩ := slots slot t near
  rcases class_eq _ related with left | right
  · have h := (recover false false ⟨slot, u⟩ left).2
    exact h.imp (congrArg Sigma.fst) (congrArg Sigma.fst)
  · cases (recover true false ⟨slot, u⟩ right).1

end Unfoldings.MetricGluing
