module

public import Mathlib.Topology.MetricSpace.Isometry

/-! Closed, isometric cell seams are constructed from equally paced closed bank curves. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {A E F X Y : Type*} [MetricSpace A] [MetricSpace E] [MetricSpace F]
  [EMetricSpace X] [EMetricSpace Y]
  (leftCell : E → X) (rightCell : F → Y) (leftBank : A → X) (rightBank : A → Y)

/-- A literal pair of original cell points at the same actual bank parameter.
Empty cell pairs are allowed; no chosen inverse or extra bank points are introduced. -/
abbrev PairedBankCellDomain :=
  {p : E × F // ∃ t, leftCell p.1 = leftBank t ∧ rightCell p.2 = rightBank t}

namespace PairedBankCellDomain

variable (left_cell_isometry : Isometry leftCell) (right_cell_isometry : Isometry rightCell)
  (same_metric : ∀ s t, edist (leftBank s) (leftBank t) = edist (rightBank s) (rightBank t))

include left_cell_isometry right_cell_isometry same_metric in
omit [MetricSpace A] in
/-- Each parameter pair has identical raw distances in its two original cells. -/
theorem coordinate_edist (p q : PairedBankCellDomain leftCell rightCell leftBank rightBank) :
    edist p.val.1 q.val.1 = edist p.val.2 q.val.2 := by
  obtain ⟨s, first_p, second_p⟩ := p.property
  obtain ⟨t, first_q, second_q⟩ := q.property
  exact (left_cell_isometry.edist_eq _ _).symm.trans
    ((congrArg₂ edist first_p first_q).trans ((same_metric s t).trans
      ((congrArg₂ edist second_p second_q).symm.trans (right_cell_isometry.edist_eq _ _))))

include left_cell_isometry right_cell_isometry same_metric in
omit [MetricSpace A] in
/-- The paired domain's product metric is exactly its original left-cell metric. -/
theorem left_isometry : Isometry (fun p : PairedBankCellDomain leftCell rightCell
    leftBank rightBank => p.val.1) := by
  intro p q
  change edist p.val.1 q.val.1 = edist p.val q.val
  rw [Prod.edist_eq, ← coordinate_edist leftCell rightCell leftBank rightBank
    left_cell_isometry right_cell_isometry same_metric p q, max_self]

include left_cell_isometry right_cell_isometry same_metric in
omit [MetricSpace A] in
/-- The same domain also maps isometrically to its original right cell. -/
theorem right_isometry : Isometry (fun p : PairedBankCellDomain leftCell rightCell
    leftBank rightBank => p.val.2) := by
  intro p q
  change edist p.val.2 q.val.2 = edist p.val q.val
  rw [Prod.edist_eq, coordinate_edist leftCell rightCell leftBank rightBank
    left_cell_isometry right_cell_isometry same_metric p q, max_self]

variable (left_closed : IsClosed (Set.range leftCell))
  (right_closed : IsClosed (Set.range rightCell))
  (left_bank_closed : Topology.IsClosedEmbedding leftBank)
  (right_bank_closed : Topology.IsClosedEmbedding rightBank)

include left_cell_isometry right_closed left_bank_closed right_bank_closed in
omit [MetricSpace F] in
/-- The actual left seam image is closed, including at finite endpoints and on whole tails. -/
theorem left_range_closed : IsClosed (Set.range
    (fun p : PairedBankCellDomain leftCell rightCell leftBank rightBank => p.val.1)) := by
  have description : Set.range
      (fun p : PairedBankCellDomain leftCell rightCell leftBank rightBank => p.val.1) =
      leftCell ⁻¹' (leftBank '' (rightBank ⁻¹' Set.range rightCell)) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨t, first, second⟩ := q.property
      exact ⟨t, ⟨q.val.2, second⟩, first.symm⟩
    · rintro ⟨t, ⟨q, second⟩, first⟩
      exact ⟨⟨(p, q), t, first.symm, second⟩, rfl⟩
  rw [description]
  exact (left_bank_closed.isClosedMap _
    (right_closed.preimage right_bank_closed.continuous)).preimage left_cell_isometry.continuous

include right_cell_isometry left_closed left_bank_closed right_bank_closed in
omit [MetricSpace E] in
/-- The actual right seam image is closed as well, with the original parameter retained. -/
theorem right_range_closed : IsClosed (Set.range
    (fun p : PairedBankCellDomain leftCell rightCell leftBank rightBank => p.val.2)) := by
  have description : Set.range
      (fun p : PairedBankCellDomain leftCell rightCell leftBank rightBank => p.val.2) =
      rightCell ⁻¹' (rightBank '' (leftBank ⁻¹' Set.range leftCell)) := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨t, first, second⟩ := p.property
      exact ⟨t, ⟨p.val.1, first⟩, second.symm⟩
    · rintro ⟨t, ⟨p, first⟩, second⟩
      exact ⟨⟨(p, q), t, first, second.symm⟩, rfl⟩
  rw [description]
  exact (right_bank_closed.isClosedMap _
    (left_closed.preimage left_bank_closed.continuous)).preimage right_cell_isometry.continuous

end PairedBankCellDomain
end Unfoldings
