module

public import Unfoldings.Metric.BankStackAddressRecovery

/-! Unique original marks identify exactly two-point ordinary bank-stack seam classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)
  (X : Option G → Type*)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- Select the original left or right endpoint of one consecutive seam. -/
def bankStackEndpoint (side : Bool) (slot : BankStackSlot stack) (t : Parameter slot.1) :
    Total X :=
  if side then bankStackRight X stack base gap slot t else bankStackLeft X stack base gap slot t

/-- The selected endpoint retains the original unglued marked-bank address. -/
def bankStackEndpointAddress (side : Bool) (slot : BankStackSlot stack)
    (t : Parameter slot.1) : BankStackAddress (G := G) (Parameter := Parameter) :=
  if side then bankStackRightAddress stack slot t else bankStackLeftAddress stack slot t

/-- All endpoint addresses are distinct when each original stack has no repeated source. -/
theorem bankStackEndpointAddress_injective (nodup : ∀ e, (stack e).Nodup) : Function.Injective
    (fun p : Bool × (Σ slot : BankStackSlot stack, Parameter slot.1) =>
      bankStackEndpointAddress stack p.1 p.2.1 p.2.2) := by
  rintro ⟨side, slot, t⟩ ⟨other_side, other, s⟩ equal
  cases side <;> cases other_side
  · exact congrArg (fun p => (false, p)) (bankStackLeftAddress_injective stack nodup equal)
  · exact (bankStackLeftAddress_ne_rightAddress stack _ _ _ _ equal).elim
  · exact (bankStackLeftAddress_ne_rightAddress stack _ _ _ _ equal.symm).elim
  · exact congrArg (fun p => (true, p)) (bankStackRightAddress_injective stack nodup equal)

/-- Either selected address names an actual original bank mark. -/
theorem bankStackEndpointAddress_valid (side : Bool) (slot : BankStackSlot stack)
    (t : Parameter slot.1) :
    BankStackAddressValid stack (bankStackEndpointAddress stack side slot t) := by
  cases side
  · exact bankStackLeftAddress_valid stack slot t
  · exact bankStackRightAddress_valid stack slot t

/-- The selected address is interpreted by the original intrinsic piece map. -/
theorem bankStackAddressPoint_endpoint (side : Bool) (slot : BankStackSlot stack)
    (t : Parameter slot.1) :
    bankStackAddressPoint stack X base gap (bankStackEndpointAddress stack side slot t)
      (bankStackEndpointAddress_valid stack side slot t) =
        bankStackEndpoint stack X base gap side slot t := by
  cases side
  · exact bankStackAddressPoint_left stack X base gap slot t
  · exact bankStackAddressPoint_right stack X base gap slot t

/-- Unique marks at one original parameter recover the endpoint side, seam slot, and time.
The competing endpoint can lie on any original attachment or at a closed endpoint. -/
theorem bankStackEndpoint_eq_of_unique (nodup : ∀ e, (stack e).Nodup)
    (slot : BankStackSlot stack) (t : Parameter slot.1)
    (unique : BankStackUniqueMarksAt stack X base gap slot.1 t)
    (side other_side : Bool) (other : BankStackSlot stack) (s : Parameter other.1)
    (equal : bankStackEndpoint stack X base gap other_side other s =
      bankStackEndpoint stack X base gap side slot t) :
    (other_side, (⟨other, s⟩ : Σ slot : BankStackSlot stack, Parameter slot.1)) =
      (side, ⟨slot, t⟩) := by
  let a := bankStackEndpointAddress stack side slot t
  have unique_at : BankStackUniqueMarksAt stack X base gap a.1 a.2.2.2 := by
    let P (p : BankStackAddress (G := G) (Parameter := Parameter)) :=
      BankStackUniqueMarksAt stack X base gap p.1 p.2.2.2
    change P (bankStackEndpointAddress stack side slot t)
    cases side
    · change P (bankStackLeftAddress stack slot t)
      unfold bankStackLeftAddress
      split <;> exact unique
    · change P (bankStackRightAddress stack slot t)
      unfold bankStackRightAddress
      split <;> exact unique
  have points := (bankStackAddressPoint_endpoint stack X base gap other_side other s).trans
    (equal.trans (bankStackAddressPoint_endpoint stack X base gap side slot t).symm)
  have addresses := bankStackAddress_eq_of_point_eq stack X base gap a.1 a.2.2.2 unique_at
    a.2.1 a.2.2.1 (bankStackEndpointAddress_valid stack side slot t)
    (bankStackEndpointAddress stack other_side other s)
    (bankStackEndpointAddress_valid stack other_side other s) points
  exact bankStackEndpointAddress_injective stack nodup addresses

/-- With unique original marks, the equivalence class of one consecutive seam consists
of exactly its two original endpoints. No final development or nonoverlap is assumed. -/
theorem bankStack_eqvGen_pair_iff (nodup : ∀ e, (stack e).Nodup)
    (slot : BankStackSlot stack) (t : Parameter slot.1)
    (unique : BankStackUniqueMarksAt stack X base gap slot.1 t) (x : Total X) :
    Relation.EqvGen
        (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
        (bankStackLeft X stack base gap slot t) x ↔
      x = bankStackLeft X stack base gap slot t ∨
        x = bankStackRight X stack base gap slot t := by
  let L := bankStackLeft X stack base gap
  let R := bankStackRight X stack base gap
  let P (y : Total X) := y = L slot t ∨ y = R slot t
  have closed (a b : Total X) (joined : bankSeams L R a b) : P a ↔ P b := by
    obtain ⟨other, s, rfl, rfl⟩ := joined
    constructor
    · rintro (first | last)
      · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
          false false other s first
        exact Or.inr (congrArg
          (fun p : Bool × (Σ slot : BankStackSlot stack, Parameter slot.1) =>
            R p.2.1 p.2.2) named)
      · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
          true false other s last
        have impossible := congrArg Prod.fst named
        cases impossible
    · rintro (first | last)
      · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
          false true other s first
        have impossible := congrArg Prod.fst named
        cases impossible
      · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
          true true other s last
        exact Or.inl (congrArg
          (fun p : Bool × (Σ slot : BankStackSlot stack, Parameter slot.1) =>
            L p.2.1 p.2.2) named)
  have preserved {a b : Total X} (related : Relation.EqvGen (bankSeams L R) a b) :
      P a ↔ P b := by
    induction related with
    | rel a b joined => exact closed a b joined
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first last => exact first.trans last
  constructor
  · intro related
    exact (preserved related).mp (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ ⟨slot, t, rfl, rfl⟩

variable [∀ i, EMetricSpace (X i)] in
/-- In an exact graft, any bank endpoint with the same metric image as an ordinary seam
recovers that seam's original slot and parameter. Either endpoint side is allowed. -/
theorem bankStackEndpoint_parameter_eq_of_point_eq (nodup : ∀ e, (stack e).Nodup)
    (exact : Exact X (bankSeams (bankStackLeft X stack base gap)
      (bankStackRight X stack base gap)))
    (slot : BankStackSlot stack) (t : Parameter slot.1)
    (unique : BankStackUniqueMarksAt stack X base gap slot.1 t)
    (other_side : Bool) (other : BankStackSlot stack) (s : Parameter other.1)
    (equal : point X (bankSeams (bankStackLeft X stack base gap)
        (bankStackRight X stack base gap)) (bankStackEndpoint stack X base gap other_side other s) =
      point X (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
        (bankStackLeft X stack base gap slot t)) :
    (⟨other, s⟩ : Σ slot : BankStackSlot stack, Parameter slot.1) = ⟨slot, t⟩ := by
  have related := exact _ _ equal.symm
  rcases (bankStack_eqvGen_pair_iff stack X base gap nodup slot t unique _).mp related with
    first | last
  · exact congrArg Prod.snd (bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      false other_side other s first)
  · exact congrArg Prod.snd (bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      true other_side other s last)

end Unfoldings.MetricGluing
