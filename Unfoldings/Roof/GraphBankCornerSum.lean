module

public import Unfoldings.Roof.GraphBankSharpBudget

/-! Rewrite the upper-bank balance as the sum over its literal incident triangle corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- Rewrite a regional angle sum along any trace as its incident original corner weights. -/
theorem sum_regionalAngleExcess_on_trace_eq_cornerSum (upper : Set Face) (path : Set Plane) :
    (∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ path then K.regionalAngleExcess upper w else 0) =
    ∑ d : C.Corner, if (K.projectedTriangle d.1).vertex d.2 ∈ path ∧ d.1 ∈ upper
      then (C.triangle d.1).cornerAngle d.2 - (K.projectedTriangle d.1).cornerAngle d.2 else 0 := by
  let term (d : C.Corner) :=
    if d.1 ∈ upper then (C.triangle d.1).cornerAngle d.2 - (K.projectedTriangle d.1).cornerAngle d.2 else 0
  let base := C.vertexOfCorner Set.univ
  let marked := Finset.univ.filter (fun w : C.Vertex Set.univ => K.projectedVertex w ∈ path)
  have sum := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset C.Corner) marked base term
  rw [Finset.sum_filter] at sum
  simp only [Finset.sum_filter] at sum
  refine Eq.trans ?_ (sum.trans ?_)
  · unfold regionalAngleExcess TriangleComplex.regionalCornerSum
    apply Finset.sum_congr rfl
    intro w _
    by_cases contact : K.projectedVertex w ∈ path
    · rw [ite_eq_left contact, ite_eq_left contact]
      apply Finset.sum_congr rfl
      intro d _
      change (if d.1 ∈ upper ∧ base d = w then _ else 0) = _
      by_cases at_w : base d = w <;> by_cases selected : d.1 ∈ upper <;>
        simp only [term, at_w, selected, ite_true, ite_false, and_true, and_false]
    · rw [ite_eq_right contact, ite_eq_right contact]
  · apply Finset.sum_congr rfl
    intro d _
    have position : K.projectedVertex (base d) = (K.projectedTriangle d.1).vertex d.2 :=
      K.projectedVertex_ofCorner d.1 d.2
    have inside : base d ∈ marked ↔ (K.projectedTriangle d.1).vertex d.2 ∈ path := by
      simp only [marked, Finset.mem_filter, Finset.mem_univ, true_and, position]
    change (if base d ∈ marked then term d else 0) =
      (if (K.projectedTriangle d.1).vertex d.2 ∈ path ∧ d.1 ∈ upper then _ else 0)
    by_cases member : (K.projectedTriangle d.1).vertex d.2 ∈ path <;>
      by_cases selected : d.1 ∈ upper <;>
      simp only [inside, member, selected, term, ite_true, ite_false, true_and, false_and,
        and_true, and_false]


open Classical in
/-- The upper-bank sum is precisely the fine corner discrepancy on that side. -/
theorem graphBankAngleSum_upper_eq_cornerSum (f : ℝ → ℝ) (sample : Face → Plane) (a b : ℝ) :
    K.graphBankAngleSum f sample a b false =
    ∑ d : C.Corner, if (K.projectedTriangle d.1).vertex d.2 ∈ graphPoint f '' Set.Ioo a b ∧
        d.1 ∈ facesAboveGraph sample f a b
      then (C.triangle d.1).cornerAngle d.2 - (K.projectedTriangle d.1).cornerAngle d.2 else 0 := by
  unfold graphBankAngleSum
  simp only [Bool.false_eq_true, ite_false, add_zero]
  exact K.sum_regionalAngleExcess_on_trace_eq_cornerSum _ _

end Unfoldings.ConvexRoof
