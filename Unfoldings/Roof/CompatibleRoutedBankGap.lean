module

public import Unfoldings.Roof.RadialBankOpeningGap
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Actual compatible routed banks construct complete intrinsic opening gaps at uniform budgets. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

open PolygonalChain

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} {Q : ConvexRoof D}
  {φ η γ c : ℝ} {retain : Set D.Seam} {m : ℕ} {full : (D.boundarySystem retain).Chain m}
  {control : Plane}

/-- Routing, physical comparisons and a small opening budget construct a complete Jordan gap
between the actual continued intrinsic bank and its opened bank, including both infinite tails. -/
theorem exists_intrinsicBank_opening_gap
    (data : Q.RadialBankComparisons φ η γ retain full control)
    (follows : R.Follows (Q.folding.projectedBoundaryChain full))
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    (nonnegative : 0 ≤ η) (cos_positive : 0 < c) (normal : ∀ f, c ≤ Q.normal f 2)
    (rolling : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) <
      Real.cos (2 * annularHistoryAngle (a / b) β) / 4)
    (events : List (Opening m))
    (circle_budget : 3 * openingBudget events <
      (Real.cos (2 * annularHistoryAngle (a / b) β) / 2) ^ 2)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    let bank := (D.boundaryChainRoll full).outgoingRay
    ∃ gap : Set ℂ,
      IsClosed gap ∧ frontier gap = bank.carrier ∪ (bank.openings events).carrier ∧
      bank.carrier ∩ (bank.openings events).carrier = {bank.start} ∧
      (interior gap).Nonempty ∧ closure (interior gap) = gap ∧
      CompleteSpace (PolygonalPoint gap) ∧ ContractibleSpace (PolygonalPoint gap) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        gap = ⋃ i, cells i := by
  let d := Real.cos (2 * annularHistoryAngle (a / b) β)
  let loss := radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)
  have dpos : 0 < d := fine_annular_radial_margin_pos small
  have dsmall : d ≤ 1 := Real.cos_le_one _
  have ratios := Q.projectedMetricStretch_bounds cos_positive normal (full.point 0)
  have loss_nonnegative : 0 ≤ loss := radialBlockError_nonneg (ratios.1.trans ratios.2)
    nonnegative (inv_nonneg.mpr data.gamma_positive.le) (Real.sqrt_nonneg (1 - γ ^ 2))
    (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
  have remaining : d / 2 ≤ (d - loss) / (1 + loss) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + loss)).mpr
    have product := mul_nonneg (sub_nonneg.mpr dsmall) loss_nonnegative
    change loss < d / 4 at rolling
    nlinarith
  let κ : ℝ≥0 := ⟨d / 2, by positivity⟩
  have kpos : 0 < κ := by change 0 < d / 2; positivity
  have ksmall : κ ≤ 1 := by change d / 2 ≤ 1; linarith
  have physical_margin (j : Fin (m + 2)) (i : Fin (m + 1)) (earlier : j.val ≤ i.val) :
      d * (‖(Q.folding.projectedBoundaryChain full).vertex i.castSucc -
        (Q.folding.projectedBoundaryChain full).vertex j‖ *
          ‖(Q.folding.projectedBoundaryChain full).edge i‖) ≤
      inner ℝ ((Q.folding.projectedBoundaryChain full).vertex i.castSucc -
        (Q.folding.projectedBoundaryChain full).vertex j)
        ((Q.folding.projectedBoundaryChain full).edge i) :=
    R.follows_subhistory_radial_margin (Q.folding.projectedBoundaryChain full) follows
      positive beta acute bpos ratio inner_disk upper small j i earlier
  have rolling_small : loss < d := by change loss < d / 4 at rolling; linarith
  exact data.exists_outgoing_opening_gap nonnegative cos_positive normal physical_margin
    rolling_small κ kpos ksmall remaining events circle_budget angles_positive
    first at_start source_hinge

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
