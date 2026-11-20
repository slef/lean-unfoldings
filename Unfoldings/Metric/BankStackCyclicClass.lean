module

public import Unfoldings.Metric.BankStackEndpointExistence
public import Unfoldings.Metric.BankStackIncidentSlots
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Topology.UnitInterval

/-! Exact center classes and incident attachments of a cyclic fan of bank-stack pieces. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "EndAt" => bankStackEndpoint stack X base gap
local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))
local notation "Banks" => bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap)

/-- The cyclic list of original centers and the precise two-sided stack seams between them. -/
structure BankStackCyclicClass (n : ℕ) where
  center : Fin (n + 1) → Total X
  time : Fin (n + 1) → Time
  side : Fin (n + 1) → Bool
  first (j : Fin (n + 1)) : EndAt (side j) (time j).1 (time j).2 = center j
  next (j : Fin (n + 1)) : EndAt (!(side j)) (time j).1 (time j).2 =
    center (finRotate (n + 1) j)
  incident (j : Fin (n + 1)) (flag : Bool) (s : Time) :
    EndAt flag s.1 s.2 = center j → ∃ k, s = time k

namespace BankStackCyclicClass

variable {X stack base gap} {n : ℕ} (A : BankStackCyclicClass X stack base gap n)

theorem related_next (j : Fin (n + 1)) :
    Relation.EqvGen Banks (A.center j) (A.center (finRotate (n + 1) j)) := by
  rw [← A.first j, ← A.next j]
  cases h : A.side j
  · exact Relation.EqvGen.rel _ _ ⟨(A.time j).1, (A.time j).2, rfl, rfl⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      ⟨(A.time j).1, (A.time j).2, rfl, rfl⟩)

theorem related (j : Fin (n + 1)) : Relation.EqvGen Banks (A.center 0) (A.center j) := by
  refine Fin.induction ?_ (fun i ih => ?_) j
  · exact Relation.EqvGen.refl _
  · have step := A.related_next i.castSucc
    have advance : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [advance] at step
    exact Relation.EqvGen.trans _ _ _ ih step

theorem has_center_of_endpoint {s : Time} (named : ∃ k, s = A.time k) (flag : Bool) :
    ∃ j, EndAt flag s.1 s.2 = A.center j := by
  obtain ⟨k, rfl⟩ := named
  by_cases same : flag = A.side k
  · exact ⟨k, same.symm ▸ A.first k⟩
  · have opposite : flag = !(A.side k) := by cases flag <;> cases h : A.side k <;> simp_all
    exact ⟨finRotate (n + 1) k, opposite.symm ▸ A.next k⟩

/-- The metric-independent seam class consists of precisely the listed original centers. -/
theorem eqvGen_iff (b : Total X) :
    Relation.EqvGen Banks (A.center 0) b ↔ ∃ j, b = A.center j := by
  let named (a : Total X) := ∃ j, a = A.center j
  have preserved {a b : Total X} (h : Relation.EqvGen Banks a b) : named a ↔ named b := by
    induction h with
    | rel a b h =>
      obtain ⟨s, t, rfl, rfl⟩ := h
      constructor
      · rintro ⟨j, eq⟩
        exact A.has_center_of_endpoint (A.incident j false ⟨s, t⟩ eq) true
      · rintro ⟨j, eq⟩
        exact A.has_center_of_endpoint (A.incident j true ⟨s, t⟩ eq) false
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact ⟨fun h => (preserved h).mp ⟨0, rfl⟩, fun ⟨j, eq⟩ => eq.symm ▸ A.related j⟩

variable (old new : Total X) (roof : Fin (n + 1) → Total X)
  (entrance exit closure : Σ slot : BankStackSlot stack, Parameter slot.1)
  (between : Fin n → Σ slot : BankStackSlot stack, Parameter slot.1)

def runCenter (i : Fin (n + 3)) : Total X :=
  Fin.cases old (Fin.lastCases new roof) i

def middleTime (i : Fin (n + 1)) : Time := Fin.lastCases exit between i

def runTime (i : Fin (n + 3)) : Time :=
  Fin.cases entrance (Fin.lastCases closure (middleTime exit between)) i

@[simp] theorem runCenter_zero : runCenter old new roof 0 = old := rfl

@[simp] theorem runCenter_last :
    runCenter old new roof (Fin.last (n + 1)).succ = new := by
  change Fin.lastCases new roof (Fin.last (n + 1)) = new
  exact Fin.lastCases_last

@[simp] theorem runCenter_roof (i : Fin (n + 1)) :
    runCenter old new roof i.castSucc.succ = roof i := by
  change Fin.lastCases new roof i.castSucc = roof i
  exact Fin.lastCases_castSucc i

theorem runCenter_injective (roof_unique : Function.Injective roof)
    (different : old ≠ new) (old_roof : ∀ i, old ≠ roof i) (new_roof : ∀ i, new ≠ roof i) :
    Function.Injective (runCenter old new roof) := by
  have cases' (i : Fin (n + 3)) :
      i = 0 ∨ i = (Fin.last (n + 1)).succ ∨ ∃ j : Fin (n + 1), i = j.castSucc.succ := by
    refine Fin.cases (Or.inl rfl) (fun k => ?_) i
    refine Fin.lastCases (Or.inr (Or.inl rfl)) (fun l => ?_) k
    exact Or.inr (Or.inr ⟨l, rfl⟩)
  intro i j h
  rcases cases' i with rfl | rfl | ⟨i', rfl⟩ <;>
    rcases cases' j with rfl | rfl | ⟨j', rfl⟩
  · rfl
  · exact (different (by simpa only [runCenter_zero, runCenter_last] using h)).elim
  · exact (old_roof j' (by simpa only [runCenter_zero, runCenter_roof] using h)).elim
  · exact (different (by simpa only [runCenter_zero, runCenter_last] using h.symm)).elim
  · rfl
  · exact (new_roof j' (by simpa only [runCenter_last, runCenter_roof] using h)).elim
  · exact (old_roof i' (by simpa only [runCenter_zero, runCenter_roof] using h.symm)).elim
  · exact (new_roof i' (by simpa only [runCenter_last, runCenter_roof] using h.symm)).elim
  · have same := roof_unique (by simpa only [runCenter_roof] using h)
    exact congrArg (fun k : Fin (n + 1) => k.castSucc.succ) same

@[simp] theorem runTime_zero : runTime entrance exit closure between 0 = entrance := rfl

@[simp] theorem runTime_closure :
    runTime entrance exit closure between (Fin.last (n + 1)).succ = closure := by
  change Fin.lastCases closure (middleTime exit between) (Fin.last (n + 1)) = closure
  exact Fin.lastCases_last

private theorem runTime_roof (i : Fin (n + 1)) :
    runTime entrance exit closure between i.castSucc.succ = middleTime exit between i := by
  change Fin.lastCases closure (middleTime exit between) i.castSucc = middleTime exit between i
  exact Fin.lastCases_castSucc i

@[simp] theorem runTime_exit :
    runTime entrance exit closure between (Fin.last n).castSucc.succ = exit :=
  (runTime_roof entrance exit closure between (Fin.last n)).trans Fin.lastCases_last

@[simp] theorem runTime_between (i : Fin n) :
    runTime entrance exit closure between i.castSucc.castSucc.succ = between i :=
  (runTime_roof entrance exit closure between i.castSucc).trans (Fin.lastCases_castSucc i)

def runSide (i : Fin (n + 3)) : Bool :=
  Fin.cases true (Fin.lastCases false (fun _ => true)) i

@[simp] theorem runSide_zero : runSide (0 : Fin (n + 3)) = true := rfl

@[simp] theorem runSide_last : runSide (Fin.last (n + 1)).succ = false := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) (Fin.last (n + 1)) = false
  exact Fin.lastCases_last

@[simp] theorem runSide_roof (i : Fin (n + 1)) : runSide i.castSucc.succ = true := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) i.castSucc = true
  exact Fin.lastCases_castSucc i

-- Bundle the dependent slot and parameter so they rewrite together.
def endpointAtTime (flag : Bool) (s : Σ slot : BankStackSlot stack, Parameter slot.1) :
    Total X := EndAt flag s.1 s.2

/-- The first signed slot can come from the opposite side of an original source tip. -/
def runSideWithEntry (entrySide : Bool) (i : Fin (n + 3)) : Bool :=
  Fin.cases entrySide (Fin.lastCases false (fun _ => true)) i

@[simp] theorem runSideWithEntry_zero (entrySide : Bool) :
    runSideWithEntry entrySide (0 : Fin (n + 3)) = entrySide := rfl

@[simp] theorem runSideWithEntry_last (entrySide : Bool) :
    runSideWithEntry entrySide (Fin.last (n + 1)).succ = false := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) (Fin.last (n + 1)) = false
  exact Fin.lastCases_last

@[simp] theorem runSideWithEntry_roof (entrySide : Bool) (i : Fin (n + 1)) :
    runSideWithEntry entrySide i.castSucc.succ = true := by
  change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) i.castSucc = true
  exact Fin.lastCases_castSucc i

/-- A roof run with its first exterior slot signed by the adjoining original piece. -/
def ofRoofRunWithEntrySide (entrySide : Bool)
    (first_old : EndAt entrySide entrance.1 entrance.2 = old)
    (first_roof : EndAt (!entrySide) entrance.1 entrance.2 = roof 0)
    (step_left : ∀ j, EndAt true (between j).1 (between j).2 = roof j.castSucc)
    (step_right : ∀ j, EndAt false (between j).1 (between j).2 = roof j.succ)
    (last_roof : EndAt true exit.1 exit.2 = roof (Fin.last n))
    (last_new : EndAt false exit.1 exit.2 = new)
    (closing_old : EndAt true closure.1 closure.2 = old)
    (closing_new : EndAt false closure.1 closure.2 = new)
    (old_incident : ∀ flag (s : Time), EndAt flag s.1 s.2 = old → s = entrance ∨ s = closure)
    (new_incident : ∀ flag (s : Time), EndAt flag s.1 s.2 = new → s = exit ∨ s = closure)
    (roof_incident : ∀ (j : Fin (n + 1)) flag (s : Time), EndAt flag s.1 s.2 = roof j →
      s = entrance ∨ s = exit ∨ ∃ k, s = between k) :
    BankStackCyclicClass X stack base gap (n + 2) where
  center := runCenter old new roof
  time := runTime entrance exit closure between
  side := runSideWithEntry entrySide
  first := fun i => by
    change endpointAtTime (X := X) (stack := stack) (base := base) (gap := gap) (runSideWithEntry entrySide i)
      (runTime entrance exit closure between i) = runCenter old new roof i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact first_old
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [runSideWithEntry_last, runTime_closure, runCenter_last]
        exact closing_new
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · rw [runSideWithEntry_roof, runTime_exit, runCenter_roof]
          exact last_roof
        · rw [runSideWithEntry_roof, runTime_between, runCenter_roof]
          exact step_left l
  next := fun i => by
    change endpointAtTime (X := X) (stack := stack) (base := base) (gap := gap) (!(runSideWithEntry entrySide i))
      (runTime entrance exit closure between i) = runCenter old new roof (finRotate _ i)
    have one : finRotate (n + 3) (0 : Fin (n + 3)) = (0 : Fin (n + 2)).succ :=
      finRotate_of_lt (Nat.zero_lt_succ _)
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [one]
      have index : (0 : Fin (n + 2)).succ = (0 : Fin (n + 1)).castSucc.succ := Fin.ext rfl
      rw [index]
      rw [runSideWithEntry_zero, runTime_zero, runCenter_roof]
      exact first_roof
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · have wrap : finRotate (n + 3) (Fin.last (n + 1)).succ = 0 :=
          (congrArg (finRotate (n + 3)) (Fin.succ_last (n + 1))).trans finRotate_last
        rw [wrap]
        rw [runSideWithEntry_last, Bool.not_false, runTime_closure, runCenter_zero]
        exact closing_old
      · have advance : finRotate (n + 3) k.castSucc.succ = k.succ.succ :=
          finRotate_of_lt (Nat.succ_lt_succ k.isLt)
        rw [advance]
        refine Fin.lastCases ?_ (fun l => ?_) k
        · have same : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
          rw [same]
          rw [runSideWithEntry_roof, Bool.not_true, runTime_exit, runCenter_last]
          exact last_new
        · have same : l.castSucc.succ.succ = l.succ.castSucc.succ := Fin.ext rfl
          rw [same]
          rw [runSideWithEntry_roof, Bool.not_true, runTime_between, runCenter_roof]
          exact step_right l
  incident := fun i flag s equal => by
    have at_entrance (h : s = entrance) : ∃ k, s = runTime entrance exit closure between k :=
      ⟨0, h⟩
    have at_closure (h : s = closure) : ∃ k, s = runTime entrance exit closure between k :=
      ⟨(Fin.last (n + 1)).succ, by simpa only [runTime_closure] using h⟩
    have at_exit (h : s = exit) : ∃ k, s = runTime entrance exit closure between k :=
      ⟨(Fin.last n).castSucc.succ, by simpa only [runTime_exit] using h⟩
    revert equal
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h
      exact (old_incident flag s h).elim at_entrance at_closure
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · intro h
        exact (new_incident flag s (by simpa only [runCenter_last] using h)).elim at_exit at_closure
      · intro h
        rcases roof_incident k flag s (by simpa only [runCenter_roof] using h) with a | b | ⟨l, c⟩
        · exact at_entrance a
        · exact at_exit b
        · exact ⟨l.castSucc.castSucc.succ, by simpa only [runTime_between] using c⟩

/-- Make a cyclic seam class from the linear run of roof wedges between two gap bends.
The outgoing attachment closes the cycle by joining those two bends. -/
def ofRoofRun
    (first_old : EndAt true entrance.1 entrance.2 = old)
    (first_roof : EndAt false entrance.1 entrance.2 = roof 0)
    (step_left : ∀ j, EndAt true (between j).1 (between j).2 = roof j.castSucc)
    (step_right : ∀ j, EndAt false (between j).1 (between j).2 = roof j.succ)
    (last_roof : EndAt true exit.1 exit.2 = roof (Fin.last n))
    (last_new : EndAt false exit.1 exit.2 = new)
    (closing_old : EndAt true closure.1 closure.2 = old)
    (closing_new : EndAt false closure.1 closure.2 = new)
    (old_incident : ∀ flag (s : Time), EndAt flag s.1 s.2 = old → s = entrance ∨ s = closure)
    (new_incident : ∀ flag (s : Time), EndAt flag s.1 s.2 = new → s = exit ∨ s = closure)
    (roof_incident : ∀ (j : Fin (n + 1)) flag (s : Time), EndAt flag s.1 s.2 = roof j →
      s = entrance ∨ s = exit ∨ ∃ k, s = between k) :
    BankStackCyclicClass X stack base gap (n + 2) :=
  ofRoofRunWithEntrySide old new roof entrance exit closure between true first_old first_roof
    step_left step_right last_roof last_new closing_old closing_new old_incident new_incident
    roof_incident

/-- Every sufficiently near seam in an exact cyclic class has one of its marked
slot parameters, within the same arclength radius in the underlying original piece. -/
theorem exists_near_marked_slot [∀ i, EMetricSpace (X i)]
    (parameterize : ∀ j, unitInterval ≃ Parameter (A.time j).1.1)
    (at_zero : ∀ j, parameterize j 0 = (A.time j).2)
    (length : Fin (n + 1) → ℝ) (length_nonneg : ∀ j, 0 ≤ length j)
    (metric : ∀ j (t : unitInterval),
      edist (bankStackLeftCurve stack X base gap (A.time j).1 (parameterize j 0))
        (bankStackLeftCurve stack X base gap (A.time j).1 (parameterize j t)) =
          ENNReal.ofReal (t.val * length j))
    {ρ : ℝ}
    (clearance : ∀ s : Time,
      edist (point X Banks (A.center 0))
        (point X Banks (bankStackLeft X stack base gap s.1 s.2)) < ENNReal.ofReal ρ →
      ∃ u : Parameter s.1.1, Relation.EqvGen Banks (A.center 0)
        (bankStackLeft X stack base gap s.1 u) ∧
        edist (bankStackLeftCurve stack X base gap s.1 u)
          (bankStackLeftCurve stack X base gap s.1 s.2) < ENNReal.ofReal ρ)
    (s : Time) (near : edist (point X Banks (A.center 0))
      (point X Banks (bankStackLeft X stack base gap s.1 s.2)) < ENNReal.ofReal ρ) :
    ∃ (j : Fin (n + 1)) (t : unitInterval), s = ⟨(A.time j).1, parameterize j t⟩ ∧ t.val * length j < ρ := by
  obtain ⟨u, related, distance⟩ := clearance s near
  obtain ⟨i, eq⟩ := (A.eqvGen_iff _).mp related
  obtain ⟨j, named⟩ := A.incident i false ⟨s.1, u⟩ eq
  let Curve := bankStackLeftCurve stack X base gap
  have transport (x : Time) (at_origin : x = A.time j) (other : Parameter x.1.1)
      (bound : edist (Curve x.1 x.2) (Curve x.1 other) < ENNReal.ofReal ρ) :
      ∃ t : unitInterval, (⟨x.1, other⟩ : Time) = ⟨(A.time j).1, parameterize j t⟩ ∧
        t.val * length j < ρ := by
    -- Retain both dependent parameters by transporting the entire two-point assertion.
    let P (z : Time) := ∀ v : Parameter z.1.1,
      edist (Curve z.1 z.2) (Curve z.1 v) < ENNReal.ofReal ρ →
      ∃ t : unitInterval, (⟨z.1, v⟩ : Time) = ⟨(A.time j).1, parameterize j t⟩ ∧
        t.val * length j < ρ
    have valid : P (A.time j) := by
      intro v hv
      obtain ⟨t, rfl⟩ := (parameterize j).surjective v
      refine ⟨t, rfl, ?_⟩
      have close := (metric j t).symm.trans_lt ((at_zero j).symm ▸ hv)
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg t.property.1
        (length_nonneg j))).mp close
    exact (at_origin.symm ▸ valid) other bound
  obtain ⟨t, same, bound⟩ := transport ⟨s.1, u⟩ named s.2 distance
  exact ⟨j, t, (Sigma.eta s).symm.trans same, bound⟩

end BankStackCyclicClass

end Unfoldings.MetricGluing
