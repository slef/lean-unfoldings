module

public import Unfoldings.Metric.BankStackEndpointExistence

/-! Transfer named roof marks to the unique exterior slots of a bank stack. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (X : Option G → Type*)
  (stack : Edge → List G) (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "Time" => (Σ s : BankStackSlot stack, Parameter (Sigma.fst s))
local notation "Address" => BankStackAddress (G := G) (Parameter := Parameter)
local notation "Valid" => BankStackAddressValid stack
local notation "AddressOf" => bankStackEndpointAddress (Parameter := Parameter) stack
local notation "EndAt" => bankStackEndpoint stack X base gap
local notation "Mark" => bankStackAddressPoint stack X base gap

/-- A signed roof bank meets the corresponding exterior slot, even on an empty stack. -/
def bankStackRoofTime (edge : Edge) (side : Bool) (t : Parameter edge) : Time :=
  ⟨⟨edge, if side then Fin.last (stack edge).length else 0⟩, t⟩

@[simp] theorem bankStackRoofTime_address (edge : Edge) (side : Bool) (t : Parameter edge) :
    let q := bankStackRoofTime stack edge side t
    AddressOf side q.1 q.2 = ⟨edge, none, side, t⟩ := by
  cases side <;> simp [bankStackRoofTime, bankStackEndpointAddress, bankStackLeftAddress,
    bankStackRightAddress]

/-- If a roof copy has two specified marks, their exterior slots are its exact incidences. -/
theorem bankStackEndpoint_eq_base_iff_two_marks
    (nodup : ∀ e, (stack e).Nodup) (x : X none)
    (a b : Edge) (left right : Bool) (s : Parameter a) (t : Parameter b)
    (names : ∀ e side (r : Parameter e), base e side r = x ↔
      ((⟨e, r⟩ : Σ e : Edge, Parameter e) = ⟨a, s⟩ ∧ side = left) ∨
      ((⟨e, r⟩ : Σ e : Edge, Parameter e) = ⟨b, t⟩ ∧ side = right))
    (flag : Bool) (q : Time) :
    EndAt flag q.1 q.2 = ⟨none, x⟩ ↔
      (flag = left ∧ q = bankStackRoofTime stack a left s) ∨
      (flag = right ∧ q = bankStackRoofTime stack b right t) := by
  let mark (e : Edge) (side : Bool) (r : Parameter e) : Address := ⟨e, none, side, r⟩
  let first := bankStackRoofTime stack a left s
  let last := bankStackRoofTime stack b right t
  have read (address : Address) (h : Valid address)
      (eq : Mark address h = ⟨none, x⟩) :
      address = mark a left s ∨ address = mark b right t := by
    obtain ⟨e, i, side, r⟩ := address
    cases i with
    | some g => cases congrArg Sigma.fst eq
    | none =>
      have at_x : base e side r = x := eq_of_heq (Sigma.mk.inj eq).2
      rcases (names e side r).mp at_x with ⟨time, flag⟩ | ⟨time, flag⟩
      · exact Or.inl (congrArg₂ (fun u v => mark u.1 v u.2) time flag)
      · exact Or.inr (congrArg₂ (fun u v => mark u.1 v u.2) time flag)
  constructor
  · intro equal
    let addr := AddressOf flag q.1 q.2
    let valid := bankStackEndpointAddress_valid stack flag q.1 q.2
    rcases read addr valid ((bankStackAddressPoint_endpoint stack X base gap flag q.1 q.2).trans
      equal) with left_eq | right_eq
    · have same : (flag, q) = (left, first) := bankStackEndpointAddress_injective stack nodup
        (left_eq.trans (bankStackRoofTime_address stack a left s).symm)
      exact Or.inl ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · have same : (flag, q) = (right, last) := bankStackEndpointAddress_injective stack nodup
        (right_eq.trans (bankStackRoofTime_address stack b right t).symm)
      exact Or.inr ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  · rintro (⟨flag_eq, q_eq⟩ | ⟨flag_eq, q_eq⟩)
    · rw [flag_eq, q_eq]
      exact (bankStackEndpoint_eq_of_base_address stack X base gap left first a left s
        (bankStackRoofTime_address stack a left s)).trans
        (congrArg (Sigma.mk none) ((names a left s).mpr (Or.inl ⟨rfl, rfl⟩)))
    · rw [flag_eq, q_eq]
      exact (bankStackEndpoint_eq_of_base_address stack X base gap right last b right t
        (bankStackRoofTime_address stack b right t)).trans
        (congrArg (Sigma.mk none) ((names b right t).mpr (Or.inr ⟨rfl, rfl⟩)))

end Unfoldings.MetricGluing
