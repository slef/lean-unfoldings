module

public import Unfoldings.Metric.BankStackCyclicClass

/-! A cyclic bank class with one gap bend and a run of original roof wedges. -/

@[expose] public section

namespace Unfoldings.MetricGluing.BankStackCyclicClass

variable {G Edge : Type*} {Parameter : Edge → Type*} {X : Option G → Type*}
  {stack : Edge → List G} {base : ∀ e, Bool → Parameter e → X none}
  {gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g)} {n : ℕ}

local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))
local notation "At" => endpointAtTime (base := base) (gap := gap)

variable (bend : Total X) (roof : Fin (n + 1) → Total X)
  (entrance closure : Σ slot : BankStackSlot stack, Parameter slot.1)
  (between : Fin n → Σ slot : BankStackSlot stack, Parameter slot.1)

/-- Start at the gap bend, then follow the ordered roof wedges. -/
def singleCenter (i : Fin (n + 2)) : Total X := Fin.cases bend roof i

/-- The last roof wedge returns to the gap bend across the outgoing bank. -/
def singleTime (i : Fin (n + 2)) : Time :=
  Fin.cases entrance (Fin.lastCases closure between) i

def singleSide (i : Fin (n + 2)) : Bool := Fin.cases true (Fin.lastCases false (fun _ => true)) i

@[simp] theorem singleCenter_zero : singleCenter bend roof 0 = bend := rfl

@[simp] theorem singleCenter_roof (i : Fin (n + 1)) :
    singleCenter bend roof i.succ = roof i := rfl

@[simp] theorem singleTime_zero : singleTime entrance closure between 0 = entrance := rfl

@[simp] theorem singleTime_last :
    singleTime entrance closure between (Fin.last n).succ = closure := by
  change Fin.lastCases (motive := fun _ => Time) closure between (Fin.last n) = closure
  exact Fin.lastCases_last

@[simp] theorem singleTime_between (i : Fin n) :
    singleTime entrance closure between i.castSucc.succ = between i := by
  change Fin.lastCases (motive := fun _ => Time) closure between i.castSucc = between i
  exact Fin.lastCases_castSucc i

@[simp] theorem singleSide_zero : singleSide (0 : Fin (n + 2)) = true := rfl

@[simp] theorem singleSide_last : singleSide (Fin.last n).succ = false := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) (Fin.last n) = false
  exact Fin.lastCases_last

@[simp] theorem singleSide_between (i : Fin n) : singleSide i.castSucc.succ = true := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) i.castSucc = true
  exact Fin.lastCases_castSucc i

theorem singleCenter_injective (roof_unique : Function.Injective roof)
    (bend_roof : ∀ i, bend ≠ roof i) : Function.Injective (singleCenter bend roof) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact fun _ => rfl
  · exact fun equal => (bend_roof j equal).elim
  · exact fun equal => (bend_roof i equal.symm).elim
  · exact fun equal => congrArg Fin.succ (roof_unique equal)

/-- The interior slots retain the contour orientation and the two exterior slots are signed. -/
def singleSideWith (entrySide exitSide : Bool) (i : Fin (n + 2)) : Bool :=
  Fin.cases entrySide (Fin.lastCases exitSide (fun _ => true)) i

@[simp] theorem singleSideWith_zero (entrySide exitSide : Bool) :
    singleSideWith entrySide exitSide (0 : Fin (n + 2)) = entrySide := rfl

@[simp] theorem singleSideWith_last (entrySide exitSide : Bool) :
    singleSideWith entrySide exitSide (Fin.last n).succ = exitSide := by
  change Fin.lastCases (motive := fun _ => Bool) exitSide (fun _ => true) (Fin.last n) = exitSide
  exact Fin.lastCases_last

@[simp] theorem singleSideWith_between (entrySide exitSide : Bool) (i : Fin n) :
    singleSideWith entrySide exitSide i.castSucc.succ = true := by
  change Fin.lastCases (motive := fun _ => Bool) exitSide (fun _ => true) i.castSucc = true
  exact Fin.lastCases_castSucc i

/-- Construct the exact cycle with either registered orientation of its two exterior slots. -/
def ofSingleBendRunWithSides (entrySide exitSide : Bool)
    (entry_bend : At entrySide entrance = bend) (entry_roof : At (!entrySide) entrance = roof 0)
    (step_left : ∀ i, At true (between i) = roof i.castSucc)
    (step_right : ∀ i, At false (between i) = roof i.succ)
    (closing_roof : At exitSide closure = roof (Fin.last n)) (closing_bend : At (!exitSide) closure = bend)
    (bend_incident : ∀ flag (s : Time), At flag s = bend → s = entrance ∨ s = closure)
    (roof_incident : ∀ i flag (s : Time), At flag s = roof i →
      s = entrance ∨ s = closure ∨ ∃ k, s = between k) :
    BankStackCyclicClass X stack base gap (n + 1) where
  center := singleCenter bend roof
  time := singleTime entrance closure between
  side := singleSideWith entrySide exitSide
  first := fun i => by
    change At (singleSideWith entrySide exitSide i) (singleTime entrance closure between i) = singleCenter bend roof i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact entry_bend
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [singleSideWith_last, singleTime_last, singleCenter_roof] using closing_roof
      · simpa only [singleSideWith_between, singleTime_between, singleCenter_roof] using step_left k
  next := fun i => by
    change At (!(singleSideWith entrySide exitSide i)) (singleTime entrance closure between i) =
      singleCenter bend roof (finRotate _ i)
    refine Fin.cases ?_ (fun j => ?_) i
    · have next : finRotate (n + 2) (0 : Fin (n + 2)) = (0 : Fin (n + 1)).succ :=
        finRotate_of_lt (Nat.zero_lt_succ n)
      rw [next, singleCenter_roof, singleSideWith_zero, singleTime_zero]
      exact entry_roof
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · have wrap : finRotate (n + 2) (Fin.last n).succ = 0 :=
          (congrArg (finRotate (n + 2)) (Fin.succ_last n)).trans finRotate_last
        rw [wrap, singleCenter_zero, singleSideWith_last, singleTime_last]
        exact closing_bend
      · have advance : finRotate (n + 2) k.castSucc.succ = k.succ.succ :=
          finRotate_of_lt (Nat.succ_lt_succ k.isLt)
        rw [advance, singleCenter_roof, singleSideWith_between, singleTime_between, Bool.not_true]
        exact step_right k
  incident := fun i flag s equal => by
    change At flag s = singleCenter bend roof i at equal
    have entrance_mem (h : s = entrance) : ∃ k, s = singleTime entrance closure between k :=
      ⟨0, h⟩
    have closure_mem (h : s = closure) : ∃ k, s = singleTime entrance closure between k :=
      ⟨(Fin.last n).succ, (singleTime_last entrance closure between).symm ▸ h⟩
    revert equal
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun h => (bend_incident flag s h).elim entrance_mem closure_mem
    · intro h
      rcases roof_incident j flag s h with a | b | ⟨k, c⟩
      · exact entrance_mem a
      · exact closure_mem b
      · exact ⟨k.castSucc.succ, (singleTime_between entrance closure between k).symm ▸ c⟩

/-- Construct the exact cyclic class of a final child gap bend and the roof run that
returns to its outgoing side. -/
def ofSingleBendRun
    (entry_bend : At true entrance = bend) (entry_roof : At false entrance = roof 0)
    (step_left : ∀ i, At true (between i) = roof i.castSucc)
    (step_right : ∀ i, At false (between i) = roof i.succ)
    (closing_roof : At false closure = roof (Fin.last n)) (closing_bend : At true closure = bend)
    (bend_incident : ∀ flag (s : Time), At flag s = bend → s = entrance ∨ s = closure)
    (roof_incident : ∀ i flag (s : Time), At flag s = roof i →
      s = entrance ∨ s = closure ∨ ∃ k, s = between k) :
    BankStackCyclicClass X stack base gap (n + 1) :=
  ofSingleBendRunWithSides bend roof entrance closure between true false entry_bend entry_roof
    step_left step_right closing_roof closing_bend bend_incident roof_incident

end Unfoldings.MetricGluing.BankStackCyclicClass
