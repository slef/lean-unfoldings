module

public import Unfoldings.Development.NetPartition
public import Mathlib.MeasureTheory.Integral.Average

/-! From expected component charge bounds to a finite original-edge net partition. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Unfoldings.FewestNets

variable {Face : Type*} [Fintype Face] (C : TriangleComplex Face)
  {Rotation Label Polygon : Type*} [MeasurableSpace Rotation] [Fintype Polygon]
  (μ : Measure Rotation) [IsProbabilityMeasure μ]

/-- Once estimates for the individual polygon charges are available, their total
bound guarantees a partition at an admissible rotation. The conclusion counts
the exact original-face components of one labeling. -/
theorem exists_net_partition_of_expected_component_charges
    (bad : Set Rotation) (null : μ bad = 0)
    (label : Rotation → Face → Label) (charge : Polygon → Rotation → ℝ)
    (charge_integrable : ∀ p, Integrable (charge p) μ)
    (bound : Polygon → ℝ) (expected : ∀ p, (∫ r, charge p r ∂μ) ≤ bound p)
    (counting : ∀ r ∉ bad,
      (Nat.card (C.labeledSeamGraph (label r)).ConnectedComponent : ℝ) =
        2 + ∑ p, charge p r)
    (net : ∀ r ∉ bad, ∀ c : (C.labeledSeamGraph (label r)).ConnectedComponent,
      C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) ≤ 2 + ∑ p, bound p ∧ C.HasNetPartition n := by
  let count (r : Rotation) := 2 + ∑ p, charge p r
  have sum_integrable : Integrable (fun r => ∑ p, charge p r) μ :=
    integrable_finsetSum Finset.univ (fun p _ => charge_integrable p)
  have integrable : Integrable count μ := (integrable_const 2).add sum_integrable
  obtain ⟨r, good, average⟩ := exists_notMem_null_le_integral integrable null
  have integral_bound : (∫ r, count r ∂μ) ≤ 2 + ∑ p, bound p := by
    unfold count
    rw [integral_add (integrable_const 2) sum_integrable, integral_const]
    simp only [probReal_univ, one_smul]
    rw [integral_finsetSum Finset.univ (fun p _ => charge_integrable p)]
    exact add_le_add_right (Finset.sum_le_sum fun p _ => expected p) _
  refine ⟨Nat.card (C.labeledSeamGraph (label r)).ConnectedComponent, ?_, ?_⟩
  · exact (counting r good).le.trans (average.trans integral_bound)
  · exact C.hasNetPartition_card_labeledSeamGraph (label r) (net r good)

end Unfoldings.FewestNets
