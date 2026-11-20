module

public import Unfoldings.Metric.BankStackCyclicClass

/-! A cycle of original roof wedges across empty bank stacks. -/

@[expose] public section

namespace Unfoldings.MetricGluing.BankStackCyclicClass

variable {G Edge : Type*} {Parameter : Edge → Type*} {X : Option G → Type*}
  {stack : Edge → List G} {base : ∀ e, Bool → Parameter e → X none}
  {gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g)} {n : ℕ}

local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))
local notation "At" => endpointAtTime (base := base) (gap := gap)

variable (roof : Fin (n + 1) → Total X)
  (closure : Σ slot : BankStackSlot stack, Parameter slot.1)
  (between : Fin n → Σ slot : BankStackSlot stack, Parameter slot.1)

def roofTime (i : Fin (n + 1)) : Time := Fin.lastCases closure between i

def roofSide (i : Fin (n + 1)) : Bool := Fin.lastCases false (fun _ => true) i

@[simp] theorem roofTime_last : roofTime closure between (Fin.last n) = closure := by
  change Fin.lastCases (motive := fun _ => Time) closure between (Fin.last n) = closure
  exact Fin.lastCases_last

@[simp] theorem roofTime_between (i : Fin n) : roofTime closure between i.castSucc = between i := by
  change Fin.lastCases (motive := fun _ => Time) closure between i.castSucc = between i
  exact Fin.lastCases_castSucc i

@[simp] theorem roofSide_last : roofSide (Fin.last n) = false := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) (Fin.last n) = false
  exact Fin.lastCases_last

@[simp] theorem roofSide_between (i : Fin n) : roofSide i.castSucc = true := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) i.castSucc = true
  exact Fin.lastCases_castSucc i

/-- Restore a whole run of roof wedges along their otherwise empty original stacks. -/
def ofClosedRoofRun
    (step_left : ∀ i, At true (between i) = roof i.castSucc)
    (step_right : ∀ i, At false (between i) = roof i.succ)
    (closing_left : At false closure = roof (Fin.last n))
    (closing_right : At true closure = roof 0)
    (incident : ∀ i flag (s : Time), At flag s = roof i → s = closure ∨ ∃ j, s = between j) :
    BankStackCyclicClass X stack base gap n where
  center := roof
  time := roofTime closure between
  side := roofSide
  first := fun i => by
    change At (roofSide i) (roofTime closure between i) = roof i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [roofSide_last, roofTime_last] using closing_left
    · simpa only [roofSide_between, roofTime_between] using step_left j
  next := fun i => by
    change At (!(roofSide i)) (roofTime closure between i) = roof (finRotate _ i)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [finRotate_last, roofSide_last, roofTime_last, Bool.not_false] using closing_right
    · have next : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      simpa only [next, roofSide_between, roofTime_between, Bool.not_true] using step_right j
  incident := fun i flag s h => by
    rcases incident i flag s h with same | ⟨j, same⟩
    · exact ⟨Fin.last n, (roofTime_last closure between).symm ▸ same⟩
    · exact ⟨j.castSucc, (roofTime_between closure between j).symm ▸ same⟩

end Unfoldings.MetricGluing.BankStackCyclicClass
