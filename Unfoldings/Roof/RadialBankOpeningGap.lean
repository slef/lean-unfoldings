module

public import Unfoldings.Roof.RadialBankSubhistoryRolling
public import Unfoldings.Geometry.OutgoingBankRay
public import Unfoldings.Geometry.PositiveOpeningMarginGap
public import Unfoldings.Complex.BoundaryChainAperture

/-! Construct complete polygonal gaps from actual intrinsic bank rolls and physical comparisons. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.RadialBankComparisons

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η γ d c : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane} (data : K.RadialBankComparisons φ η γ retain full control)

local notation "physical" => K.folding.projectedBoundaryChain full

include data in
/-- Physical cap comparisons construct the actual complete opening gap; no length certificate,
planar embedding or preexisting gap is supplied. The tail continues the last actual rolled edge. -/
theorem exists_outgoing_opening_gap (nonnegative : 0 ≤ η) (cos_positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2)
    (all_anchors : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), j.val ≤ i.val →
      d * (‖(physical).vertex i.castSucc - (physical).vertex j‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex j) ((physical).edge i))
    (rolling : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d)
    (κ : ℝ≥0) (positive : 0 < κ) (small : κ ≤ 1)
    (remaining : (κ : ℝ) ≤
      (d - radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)))
    (events : List (Opening m))
    (circle_budget : 3 * openingBudget events < (κ : ℝ) ^ 2)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    let R := (C.boundaryChainRoll full).outgoingRay
    ∃ G : Set ℂ,
      IsClosed G ∧ frontier G = R.carrier ∪ (R.openings events).carrier ∧
      R.carrier ∩ (R.openings events).carrier = {R.start} ∧
      (interior G).Nonempty ∧ closure (interior G) = G ∧
      CompleteSpace (PolygonalPoint G) ∧ ContractibleSpace (PolygonalPoint G) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        G = ⋃ i, cells i := by
  let Q := C.boundaryChainRoll full
  have intrinsic_margin (j : Fin (m + 2)) (i : Fin (m + 1)) (earlier : j.val ≤ i.val) :
      (κ : ℝ) * (‖Q.vertex i.castSucc - Q.vertex j‖ * ‖Q.edge i‖) ≤
      inner ℝ (Q.vertex i.castSucc - Q.vertex j) (Q.edge i) :=
    (mul_le_mul_of_nonneg_right remaining
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
        (data.subhistory_margin nonnegative cos_positive normal all_anchors rolling j i earlier)
  exact Q.outgoingRay.exists_positive_opening_trace_gap_of_margin events
    (C.boundaryChainRoll_edge_ne_zero full (Fin.last m)) κ positive small
    circle_budget (Q.outgoingRay_margin intrinsic_margin)
    (Q.outgoingRay_tail_margin intrinsic_margin)
    angles_positive first at_start source_hinge

end Unfoldings.ConvexRoof.RadialBankComparisons
