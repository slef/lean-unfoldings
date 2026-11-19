module

public import Unfoldings.Metric.BankStackCurveMetric
public import Unfoldings.Metric.ClosedBankCellSeams
public import Unfoldings.Metric.MappedBankGraft
public import Unfoldings.Metric.ClosedSeamOperations
public import Unfoldings.Metric.ChangeSeams

/-! Closed-bank presentations for a stack over any finite family of original pieces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge Ambient : Type} [MetricSpace Ambient] [CompleteSpace Ambient]
  {J : Option G → Type} [∀ i, Finite (J i)] [Finite Edge]
  {Parameter : Edge → Type} [∀ e, MetricSpace (Parameter e)]
  (X : Option G → Type) [∀ i, EMetricSpace (X i)]
  (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  (cells : ∀ i, J i → Set Ambient)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (coordinates : ∀ i, Realization (fun j => cells i j) (inner i) ≃ᵢ X i)

local notation "L" => bankStackLeftPiece stack X base gap
local notation "R" => bankStackRightPiece stack X base gap
local notation "LC" => bankStackLeftCurve stack X base gap
local notation "RC" => bankStackRightCurve stack X base gap
local notation "Raw" => NestedCell (fun i j => cells i j)

variable
  (cell_isometry : ∀ i j, Isometry (fun p : cells i j =>
    coordinates i (of (fun l => cells i l) (inner i) j p)))
  (cell_closed : ∀ i j, IsClosed (cells i j))
  (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
  (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
  (base_metric : ∀ e side s t, edist (base e side s) (base e side t) =
    edist (base e false s) (base e false t))
  (gap_metric : ∀ e g h side s t, edist (gap e g h side s) (gap e g h side t) =
    edist (base e false s) (base e false t))

/-- A bank seam knows the true original pieces, cells and parameters on both sides. -/
def bankStackCellPair (slot : BankStackSlot stack) (j : J (L slot)) (k : J (R slot)) :
    BankCellPairData (cells (L slot) j) (cells (R slot) k) where
  Parameter := Parameter slot.1
  LeftSpace := X (L slot)
  RightSpace := X (R slot)
  leftCell p := coordinates (L slot) (of (fun l => cells (L slot) l) (inner (L slot)) j p)
  rightCell p := coordinates (R slot) (of (fun l => cells (R slot) l) (inner (R slot)) k p)
  left_isometry := cell_isometry _ _
  right_isometry := cell_isometry _ _
  left_closed := by
    let : CompleteSpace (cells (L slot) j) := (cell_closed _ _).isComplete.completeSpace_coe
    exact (cell_isometry _ j).isClosedEmbedding.isClosed_range
  right_closed := by
    let : CompleteSpace (cells (R slot) k) := (cell_closed _ _).isComplete.completeSpace_coe
    exact (cell_isometry _ k).isClosedEmbedding.isClosed_range
  leftBank := LC slot
  rightBank := RC slot
  left_bank_closed := bankStackLeftCurve_closed stack X base gap base_closed gap_closed slot
  right_bank_closed := bankStackRightCurve_closed stack X base gap base_closed gap_closed slot
  same_metric := bankStackCurves_same_metric stack X base gap base_metric gap_metric slot

/-- Every consecutive bank slot gives closed seams between its actual planar cells. -/
def bankStackCellClosedSeams : ClosedSeams Raw :=
  ClosedSeams.ofBankCellPairs _
    (fun b : Σ s : BankStackSlot stack, J (L s) × J (R s) => ⟨L b.1, b.2.1⟩)
    (fun b => ⟨R b.1, b.2.2⟩)
    (fun b => bankStackCellPair X stack base gap cells inner coordinates cell_isometry cell_closed
      base_closed gap_closed base_metric gap_metric b.1 b.2.1 b.2.2)

local notation "Seams" => bankStackCellClosedSeams X stack base gap cells inner coordinates
  cell_isometry cell_closed base_closed gap_closed base_metric gap_metric

/-- The closed seam presentation retains every original cell representative of a bank slot. -/
theorem bankStackCellClosedSeams_relation (x y : Total Raw) :
    (Seams).relation x y ↔
      bankSeams (bankStackLeft X stack base gap) (bankStackRight X stack base gap)
        (mappedNestedPoint cells inner coordinates x)
        (mappedNestedPoint cells inner coordinates y) := by
  constructor
  · rintro ⟨b, p, rfl, rfl⟩
    obtain ⟨t, first, second⟩ := p.property
    exact ⟨b.1, t, (congrArg (Sigma.mk (L b.1)) first).trans
      (bankStackLeft_curve stack X base gap b.1 t).symm,
      (congrArg (Sigma.mk (R b.1)) second).trans
        (bankStackRight_curve stack X base gap b.1 t).symm⟩
  · rintro ⟨slot, t, first, second⟩
    obtain ⟨⟨i, j⟩, p⟩ := x
    obtain ⟨⟨k, l⟩, q⟩ := y
    have left_named := first.trans (bankStackLeft_curve stack X base gap slot t)
    have right_named := second.trans (bankStackRight_curve stack X base gap slot t)
    have left_index : i = L slot := congrArg Sigma.fst left_named
    have right_index : k = R slot := congrArg Sigma.fst right_named
    subst i
    subst k
    have left_value : coordinates (L slot)
        (of (fun j => cells (L slot) j) (inner (L slot)) j p) = LC slot t :=
      eq_of_heq (Sigma.mk.inj_iff.mp left_named).2
    have right_value : coordinates (R slot)
        (of (fun j => cells (R slot) j) (inner (R slot)) l q) = RC slot t :=
      eq_of_heq (Sigma.mk.inj_iff.mp right_named).2
    exact ⟨⟨slot, j, l⟩, ⟨(p, q), t, left_value, right_value⟩, rfl, rfl⟩

variable [Finite G] (internal : ∀ i, ClosedSeams (fun j => cells i j))

/-- Put all internal and bank seams into the same closed-cell presentation. -/
def bankStackClosedSeams : ClosedSeams Raw :=
  (ClosedSeams.ofFamily (fun i j => cells i j) internal).sum Seams

local notation "AllSeams" => bankStackClosedSeams X stack base gap cells inner coordinates
  cell_isometry cell_closed base_closed gap_closed base_metric gap_metric internal
local notation "Left" => bankStackLeft X stack base gap
local notation "Right" => bankStackRight X stack base gap

/-- Combining the two seam families recovers exactly the mapped bank stack relation. -/
theorem bankStackClosedSeams_relation
    (internal_eq : ∀ i x y, (internal i).relation x y ↔ inner i x y)
    (x y : Total Raw) : (AllSeams).relation x y ↔
      mappedBankGraftCells cells inner coordinates Left Right x y := by
  have bank := bankStackCellClosedSeams_relation X stack base gap cells inner coordinates
    cell_isometry cell_closed base_closed gap_closed base_metric gap_metric x y
  refine (ClosedSeams.sum_relation _ _ x y).trans ?_
  constructor
  · rintro (old | new)
    · obtain ⟨i, a, b, joined, rfl, rfl⟩ := (ClosedSeams.ofFamily_relation _ _ x y).mp old
      exact NestedGlue.inside (E := fun i j => cells i j) (inner := inner) i a b
        ((internal_eq i a b).mp joined)
    · exact NestedGlue.between x y (bank.mp new)
  · intro joined
    cases joined with
    | «inside» i a b seam =>
      exact Or.inl ((ClosedSeams.ofFamily_relation _ _ _ _).mpr
        ⟨i, a, b, (internal_eq i a b).mpr seam, rfl, rfl⟩)
    | between _ _ seam => exact Or.inr (bank.mpr seam)

/-- Passing to closed seams preserves the whole intrinsic route metric. -/
def bankStackClosedSeamsIsometry
    (internal_eq : ∀ i x y, (internal i).relation x y ↔ inner i x y) :
    Realization Raw (AllSeams).relation ≃ᵢ BankStackGraft X stack base gap := by
  let exactRel := bankStackClosedSeams_relation X stack base gap cells inner coordinates
    cell_isometry cell_closed base_closed gap_closed base_metric gap_metric internal internal_eq
  exact (changeSeamsIsometryEquiv _
    (fun x y h => point_eq_of_glue _ ((exactRel x y).mp h))
    (fun x y h => point_eq_of_glue _ ((exactRel x y).mpr h))).trans
      (mappedBankGraftIsometry cells inner coordinates Left Right)

end Unfoldings.MetricGluing
