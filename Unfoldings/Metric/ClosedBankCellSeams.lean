module

public import Unfoldings.Metric.PairedBankCells
public import Unfoldings.Metric.ClosedSeams

/-! A finite family of equally paced original bank-cell pairs constructs finite closed seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

/-- Local geometric data for one actual bank attachment between two original metric cells. -/
structure BankCellPairData (E F : Type*) [MetricSpace E] [MetricSpace F] where
  Parameter : Type
  [parameterMetric : MetricSpace Parameter]
  LeftSpace : Type
  RightSpace : Type
  [leftMetric : EMetricSpace LeftSpace]
  [rightMetric : EMetricSpace RightSpace]
  leftCell : E → LeftSpace
  rightCell : F → RightSpace
  left_isometry : Isometry leftCell
  right_isometry : Isometry rightCell
  left_closed : IsClosed (Set.range leftCell)
  right_closed : IsClosed (Set.range rightCell)
  leftBank : Parameter → LeftSpace
  rightBank : Parameter → RightSpace
  left_bank_closed : Topology.IsClosedEmbedding leftBank
  right_bank_closed : Topology.IsClosedEmbedding rightBank
  same_metric : ∀ s t, edist (leftBank s) (leftBank t) = edist (rightBank s) (rightBank t)

attribute [instance] BankCellPairData.parameterMetric BankCellPairData.leftMetric
  BankCellPairData.rightMetric

namespace ClosedSeams

variable {I B : Type*} (E : I → Type*) [∀ i, MetricSpace (E i)] [Finite B]
  (left right : B → I) (data : ∀ b, BankCellPairData (E (left b)) (E (right b)))

/-- Literal paired cell points construct the domains, isometries and closed images.
No seam-domain or closedness certificate is supplied beyond the original bank geometry. -/
def ofBankCellPairs : ClosedSeams E where
  Seam := B
  Domain b := PairedBankCellDomain (data b).leftCell (data b).rightCell
    (data b).leftBank (data b).rightBank
  left := left
  right := right
  toLeft _ p := p.val.1
  toRight _ p := p.val.2
  left_isometry b := PairedBankCellDomain.left_isometry _ _ _ _
    (data b).left_isometry (data b).right_isometry (data b).same_metric
  right_isometry b := PairedBankCellDomain.right_isometry _ _ _ _
    (data b).left_isometry (data b).right_isometry (data b).same_metric
  left_closed b := PairedBankCellDomain.left_range_closed _ _ _ _
    (data b).left_isometry (data b).right_closed
    (data b).left_bank_closed (data b).right_bank_closed
  right_closed b := PairedBankCellDomain.right_range_closed _ _ _ _
    (data b).right_isometry (data b).left_closed
    (data b).left_bank_closed (data b).right_bank_closed

/-- The constructed seam relation attaches precisely the named original cell representatives
at a common actual bank parameter, including every finite endpoint and whole-tail point. -/
theorem ofBankCellPairs_relation (x y : Total E) :
    (ofBankCellPairs E left right data).relation x y ↔
      ∃ b, ∃ p : E (left b), ∃ q : E (right b), ∃ t : (data b).Parameter,
        x = ⟨left b, p⟩ ∧ y = ⟨right b, q⟩ ∧
        (data b).leftCell p = (data b).leftBank t ∧
        (data b).rightCell q = (data b).rightBank t := by
  constructor
  · rintro ⟨b, p, rfl, rfl⟩
    obtain ⟨t, first, second⟩ := p.property
    exact ⟨b, p.val.1, p.val.2, t, rfl, rfl, first, second⟩
  · rintro ⟨b, p, q, t, rfl, rfl, first, second⟩
    exact ⟨b, ⟨(p, q), t, first, second⟩, rfl, rfl⟩

end ClosedSeams
end Unfoldings.MetricGluing
