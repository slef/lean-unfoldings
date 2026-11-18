module

public import Unfoldings.Metric.BankStackGraft

/-! Typed consecutive bank curves retain the actual piece indices of every stack seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*} (stack : Edge → List G)

variable (X : Option G → Type*)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- The left piece and its whole bank curve are selected together, without dependent casts. -/
def bankStackLeftData (slot : BankStackSlot stack) : Σ i, Parameter slot.1 → X i :=
  if initial : slot.2.val = 0 then ⟨none, base slot.1 false⟩ else
    let g := (stack slot.1)[slot.2.val - 1]'(by have bound := slot.2.isLt; omega)
    ⟨some g, gap slot.1 g (List.getElem_mem _) true⟩

/-- The right piece and curve include the original final bank of an empty stack. -/
def bankStackRightData (slot : BankStackSlot stack) : Σ i, Parameter slot.1 → X i :=
  if before : slot.2.val < (stack slot.1).length then
    ⟨some ((stack slot.1)[slot.2.val]), gap slot.1 _ (List.getElem_mem before) false⟩
  else ⟨none, base slot.1 true⟩

abbrev bankStackLeftPiece (slot : BankStackSlot stack) :=
  (bankStackLeftData stack X base gap slot).1
abbrev bankStackRightPiece (slot : BankStackSlot stack) :=
  (bankStackRightData stack X base gap slot).1
abbrev bankStackLeftCurve (slot : BankStackSlot stack) :=
  (bankStackLeftData stack X base gap slot).2
abbrev bankStackRightCurve (slot : BankStackSlot stack) :=
  (bankStackRightData stack X base gap slot).2

theorem bankStackLeft_curve (slot : BankStackSlot stack) (t : Parameter slot.1) :
    bankStackLeft X stack base gap slot t =
      ⟨bankStackLeftPiece stack X base gap slot, bankStackLeftCurve stack X base gap slot t⟩ := by
  let applyData (q : Σ i, Parameter slot.1 → X i) : Total X := ⟨q.1, q.2 t⟩
  change bankStackLeft X stack base gap slot t =
    applyData (bankStackLeftData stack X base gap slot)
  unfold bankStackLeft bankStackLeftData
  split
  · simp_all only [applyData]
  · simp_all only [applyData]

theorem bankStackRight_curve (slot : BankStackSlot stack) (t : Parameter slot.1) :
    bankStackRight X stack base gap slot t =
      ⟨bankStackRightPiece stack X base gap slot, bankStackRightCurve stack X base gap slot t⟩ := by
  let applyData (q : Σ i, Parameter slot.1 → X i) : Total X := ⟨q.1, q.2 t⟩
  change bankStackRight X stack base gap slot t =
    applyData (bankStackRightData stack X base gap slot)
  unfold bankStackRight bankStackRightData
  split
  · simp_all only [applyData]
  · simp_all only [applyData]

variable [∀ e, TopologicalSpace (Parameter e)] [∀ i, TopologicalSpace (X i)]

include base gap in
/-- Closedness of actual marked banks passes to the selected left curve. -/
theorem bankStackLeftCurve_closed
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    (slot : BankStackSlot stack) :
    Topology.IsClosedEmbedding (bankStackLeftCurve stack X base gap slot) := by
  let P (q : Σ i, Parameter slot.1 → X i) := Topology.IsClosedEmbedding q.2
  change P (bankStackLeftData stack X base gap slot)
  unfold bankStackLeftData
  split
  · exact base_closed _ _
  · exact gap_closed _ _ _ _

/-- Closedness also passes to the selected right curve, including empty stacks. -/
theorem bankStackRightCurve_closed
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    (slot : BankStackSlot stack) :
    Topology.IsClosedEmbedding (bankStackRightCurve stack X base gap slot) := by
  let P (q : Σ i, Parameter slot.1 → X i) := Topology.IsClosedEmbedding q.2
  change P (bankStackRightData stack X base gap slot)
  unfold bankStackRightData
  split
  · exact gap_closed _ _ _ _
  · exact base_closed _ _

end Unfoldings.MetricGluing
