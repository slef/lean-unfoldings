module

public import Unfoldings.Metric.BankGraft
public import Mathlib.Data.List.GetD

/-! Ordered gap stacks retain every bank attachment, empty stack and closed endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w z

variable {G : Type u} {Edge : Type v} {Parameter : Edge → Type w}
  (X : Option G → Type z) [∀ i, PseudoEMetricSpace (X i)]
  (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- One original edge or whole tail, together with one consecutive stack seam. -/
abbrev BankStackSlot := Σ e, Fin ((stack e).length + 1)

/-- The first seam starts on the original first bank; each later seam starts on a gap's far bank. -/
def bankStackLeft (slot : BankStackSlot stack) (t : Parameter slot.1) : Total X :=
  if initial : slot.2.val = 0 then ⟨none, base slot.1 false t⟩ else
    let g := (stack slot.1)[slot.2.val - 1]'(by have bound := slot.2.isLt; omega)
    ⟨some g, gap slot.1 g (List.getElem_mem _) true t⟩

/-- The last seam ends on the original second bank; each earlier seam ends on the next gap. -/
def bankStackRight (slot : BankStackSlot stack) (t : Parameter slot.1) : Total X :=
  if before : slot.2.val < (stack slot.1).length then
    let g := (stack slot.1)[slot.2.val]'before
    ⟨some g, gap slot.1 g (List.getElem_mem before) false t⟩
  else ⟨none, base slot.1 true t⟩

/-- Attach all consecutive bank copies at every original parameter. Finite-edge endpoints may
have different original roof copies; the actual gap vertices determine their identifications. -/
abbrev BankStackGraft :=
  BankGraft (bankStackLeft X stack base gap) (bankStackRight X stack base gap)

omit [∀ i, PseudoEMetricSpace (X i)] in
@[simp] theorem bankStackLeft_first (e : Edge) (t : Parameter e) :
    bankStackLeft X stack base gap ⟨e, 0⟩ t = ⟨none, base e false t⟩ := by
  simp [bankStackLeft]

omit [∀ i, PseudoEMetricSpace (X i)] in
@[simp] theorem bankStackRight_last (e : Edge) (t : Parameter e) :
    bankStackRight X stack base gap ⟨e, Fin.last (stack e).length⟩ t = ⟨none, base e true t⟩ := by
  simp [bankStackRight]

omit [∀ i, PseudoEMetricSpace (X i)] in
/-- Every gap's first bank is exactly the upper end of its preceding stack seam. -/
theorem bankStackRight_at (e : Edge) (i : Fin (stack e).length) (t : Parameter e) :
    bankStackRight X stack base gap ⟨e, i.castSucc⟩ t =
      ⟨some (stack e)[i.val], gap e (stack e)[i.val] (List.getElem_mem i.isLt) false t⟩ := by
  simp [bankStackRight, i.isLt]

omit [∀ i, PseudoEMetricSpace (X i)] in
/-- Every gap's far bank is exactly the lower end of its following stack seam. -/
theorem bankStackLeft_after (e : Edge) (i : Fin (stack e).length) (t : Parameter e) :
    bankStackLeft X stack base gap ⟨e, i.succ⟩ t =
      ⟨some (stack e)[i.val], gap e (stack e)[i.val] (List.getElem_mem i.isLt) true t⟩ := by
  simp [bankStackLeft]

/-- The assembled route metric identifies each named pair of consecutive bank marks. -/
theorem bankStack_seam (e : Edge) (i : Fin ((stack e).length + 1)) (t : Parameter e) :
    point X (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
      (bankStackLeft X stack base gap ⟨e, i⟩ t) =
    point X (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
      (bankStackRight X stack base gap ⟨e, i⟩ t) :=
  bankGraft_banks_equal (bankStackLeft X stack base gap) (bankStackRight X stack base gap)
    ⟨e, i⟩ t

/-- An original edge with no positive gap simply has its original two banks restored. -/
theorem bankStack_empty (e : Edge) (empty : stack e = []) (t : Parameter e) :
    of X (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
      none (base e false t) =
    of X (bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap))
      none (base e true t) := by
  have seam := bankStack_seam X stack base gap e 0 t
  have last : bankStackRight X stack base gap ⟨e, 0⟩ t = ⟨none, base e true t⟩ := by
    simp [bankStackRight, empty]
  simpa only [of, bankStackLeft_first, last] using seam

end Unfoldings.MetricGluing
