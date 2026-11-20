module

public import Unfoldings.Metric.BankStackSingleBendCycle
public import Unfoldings.Metric.Quotient

/-! A seam in an exact named cyclic class must occur at one of its listed times. -/

@[expose] public section

namespace Unfoldings.MetricGluing.BankStackCyclicClass

variable {G Edge : Type*} {Parameter : Edge → Type*} {X : Option G → Type*}
  {stack : Edge → List G} {base : ∀ e, Bool → Parameter e → X none}
  {gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g)} {n : ℕ}

local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))
local notation "Banks" => bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap)
local notation "EndAt" => bankStackEndpoint stack X base gap

/-- Every attached seam in the metric class of a given cyclic center is listed. -/
theorem exists_time_eq_of_point_eq [∀ i, EMetricSpace (X i)] (A : BankStackCyclicClass X stack base gap n)
    (exact_glue : Exact X Banks) (b : Bool) (s : Time)
    (same : point X Banks (A.center 0) = point X Banks (EndAt b s.1 s.2)) :
    ∃ i, s = A.time i := by
  obtain ⟨j, named⟩ := (A.eqvGen_iff _).mp (exact_glue _ _ same)
  exact A.incident j b s named

/-- A predicate holding on the entry, closure and all intermediate times holds on the cycle. -/
theorem singleTime_cases (entry closure : Time) (intermediate : Fin n → Time) {P : Time → Prop}
    (at_entry : P entry) (at_closure : P closure) (between : ∀ i, P (intermediate i))
    (j : Fin (n + 2)) : P (singleTime entry closure intermediate j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [singleTime_zero] using at_entry
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [singleTime_last] using at_closure
    · simpa only [singleTime_between] using between j

/-- The two bend times, closure and intermediate roof times exhaust a run. -/
theorem runTime_cases (entry exit closure : Time) (intermediate : Fin n → Time) {P : Time → Prop}
    (at_entry : P entry) (at_exit : P exit) (at_closure : P closure)
    (between : ∀ i, P (intermediate i)) (j : Fin (n + 3)) :
    P (runTime entry exit closure intermediate j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [runTime_zero] using at_entry
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [runTime_closure] using at_closure
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [runTime_exit] using at_exit
      · simpa only [runTime_between] using between j

end Unfoldings.MetricGluing.BankStackCyclicClass
