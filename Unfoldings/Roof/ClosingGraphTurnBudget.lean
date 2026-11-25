module

public import Unfoldings.Roof.GraphEndpointBalance
public import Unfoldings.Roof.GraphClosingBend

/-! Sum the two regular links and the actual bend without losing a third endpoint allowance. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The strict graph window consists of the two open links and their bend. -/
theorem graphPoint_openWindow_eq_twoLinks {g : ℝ → ℝ} {a c b : Plane}
    (first : a 0 < c 0) (last : c 0 < b 0)
    (trace : graphPoint g '' Set.Icc (a 0) (b 0) = segment ℝ a c ∪ segment ℝ c b) :
    graphPoint g '' Set.Ioo (a 0) (b 0) =
      openSegment ℝ a c ∪ openSegment ℝ c b ∪ {c} := by
  have progress {p q : Plane} (order : p 0 < q 0) {z : Plane}
      (on_link : z ∈ openSegment ℝ p q) : z 0 ∈ Set.Ioo (p 0) (q 0) := by
    obtain ⟨t, ht, rfl⟩ := (openSegment_eq_image_lineMap ℝ p q).subset on_link
    rw [AffineMap.lineMap_apply_module']
    change p 0 < t * (q 0 - p 0) + p 0 ∧ t * (q 0 - p 0) + p 0 < q 0
    exact ⟨by linarith only [mul_pos ht.1 (sub_pos.mpr order)],
      by linarith only [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr order)]⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨t, ht, rfl⟩
    let p := graphPoint g t
    have member := trace.subset (show p ∈ graphPoint g '' Set.Icc (a 0) (b 0) from
      ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩)
    by_cases bend : p = c
    · exact Or.inr bend
    left
    rcases member with left | right
    · exact Or.inl (mem_openSegment_of_ne_left_right
        (fun eq => ht.1.ne (congrArg (fun r : Plane => r 0) eq)) (Ne.symm bend) left)
    · exact Or.inr (mem_openSegment_of_ne_left_right (Ne.symm bend)
        (fun eq => ht.2.ne (congrArg (fun r : Plane => r 0) eq.symm)) right)
  · intro z member
    have h : z 0 ∈ Set.Ioo (a 0) (b 0) := by
      rcases member with (left | right) | eq
      · have t := progress first left
        exact ⟨t.1, t.2.trans last⟩
      · have t := progress last right
        exact ⟨first.trans t.1, t.2⟩
      · exact eq.symm ▸ ⟨first, last⟩
    have on_trace : z ∈ segment ℝ a c ∪ segment ℝ c b := by
      rcases member with (left | right) | eq
      · exact Or.inl (openSegment_subset_segment ℝ a c left)
      · exact Or.inr (openSegment_subset_segment ℝ c b right)
      · exact Or.inl (eq.symm ▸ right_mem_segment ℝ a c)
    obtain ⟨t, _, rfl⟩ := trace.symm.subset on_trace
    exact ⟨t, h, rfl⟩

open Classical in
set_option maxHeartbeats 1000000 in
/-- With both open links regular, the full closing-graph sum is bounded by
one shared straight-link budget and the one actual bend error. -/
theorem abs_sum_graphClosing_errors_le {g : ℝ → ℝ} (hg : Continuous g)
    {a c b : Plane} (first : a 0 < c 0) (last : c 0 < b 0)
    (trace : graphPoint g '' Set.Icc (a 0) (b 0) = segment ℝ a c ∪ segment ℝ c b)
    (inside : graphPoint g '' Set.Icc (a 0) (b 0) ⊆ interior K.footprint)
    (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a 0 ∧ z 0 ≠ b 0)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier)
      (graphPoint g '' Set.Icc (a 0) (b 0)))
    (first_regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ a c →
      K.HasRegularSectionSlopes w (c - a))
    (last_regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ c b →
      K.HasRegularSectionSlopes w (b - c))
    (w : C.Vertex Set.univ) (marked : K.projectedVertex w = c) (f : Face)
    (slopes : ∀ j i, C.vertexOfCorner Set.univ (j, i) = w → K.normalSlope j = K.normalSlope f)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    let U := facesAboveGraph sample g (a 0) (b 0)
    |∑ v : C.Vertex Set.univ, if K.projectedVertex v ∈ graphPoint g '' Set.Ioo (a 0) (b 0) then
      K.regionalAngleExcess U v else 0| ≤
      sin φ * (2 * φ + tan φ * ‖NormedSpace.normalize (c - a) - NormedSpace.normalize (b - c)‖) +
      |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) - angle (c - a) (b - c)| := by
  let V := C.Vertex Set.univ
  let I := {v : V // K.projectedVertex v ∈ openSegment ℝ a c}
  let J := {v : V // K.projectedVertex v ∈ openSegment ℝ c b}
  let U := facesAboveGraph sample g (a 0) (b 0)
  let G := K.regionalAngleExcess U
  let dom := graphPoint g '' Set.Ioo (a 0) (b 0)
  let term (v : V) := if K.projectedVertex v ∈ dom then G v else 0
  let p (v : V) := K.projectedVertex v ∈ openSegment ℝ a c
  let q (v : V) := K.projectedVertex v ∈ openSegment ℝ c b
  have bound (v : V) : |term v| ≤ (if p v then |G v| else 0) +
      (if q v then |G v| else 0) + (if v = w then |G w| else 0) := by
    have decide_dom : K.projectedVertex v ∈ dom ↔ p v ∨ q v ∨ v = w := by
      change K.projectedVertex v ∈ graphPoint g '' Set.Ioo (a 0) (b 0) ↔ _
      have at_bend : K.projectedVertex v = c ↔ v = w := by
        rw [← marked, K.projectedVertex_injective.eq_iff]
      simp only [graphPoint_openWindow_eq_twoLinks first last trace, Set.mem_union, Set.mem_singleton_iff,
        at_bend, or_assoc, p, q]
    unfold term
    by_cases eq : v = w
    · subst v
      rw [ite_eq_left (decide_dom.mpr (Or.inr (Or.inr rfl))), ite_eq_left rfl]
      have positive (condition : Prop) [Decidable condition] : 0 ≤ (if condition then |G w| else 0) := by
        split <;> positivity
      linarith only [positive (p w), positive (q w)]
    · by_cases hp : p v <;> by_cases hq : q v <;>
        simp only [decide_dom, hp, hq, eq, ite_true, ite_false, true_or, false_or, or_false,
          abs_zero, add_zero, zero_add, le_refl]; linarith only [abs_nonneg (G v)]
  have links := K.sum_abs_graphClosingLink_excess_le hg first last trace inside sample sample_in
    endpoints aligned first_regular last_regular nonnegative small tilt
  have at_bend := K.abs_graphClosingBend_excess_eq hg first last trace sample sample_in endpoints
    aligned w marked (inside (trace.symm.subset (Or.inl (right_mem_segment ℝ a c)))) f slopes
  have sum_p : (∑ v : V, if p v then |G v| else 0) = ∑ v : I, |G v.val| := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp [p]) _
  have sum_q : (∑ v : V, if q v then |G v| else 0) = ∑ v : J, |G v.val| := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp [q]) _
  change |∑ v : V, term v| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun v _ => bound v).trans ?_)
  simp only [Finset.sum_add_distrib, sum_p, sum_q, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  change (∑ v : I, |G v.val|) + (∑ v : J, |G v.val|) + |G w| ≤ _
  exact add_le_add links at_bend.le

end Unfoldings.ConvexRoof
