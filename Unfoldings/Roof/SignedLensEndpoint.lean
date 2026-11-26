module

public import Unfoldings.Roof.GraphLensEndpointLift
public import Unfoldings.Roof.RadialClosingEndpoint
public import Unfoldings.Topology.GraphLensEndpointSign

/-! The endpoint of an actual lens contributes the pole-aligned heading of its closing ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

set_option maxHeartbeats 1300000 in
/-- Compute the signed contribution of one trimmed lens endpoint. The
closing edge's active support fixes the normal used for both heading errors. -/
theorem graphLensSign_mul_regionalAngleExcess_eq_endpoint {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (jordan : Schoenflies.IsJordanCurve (graphLens f g a b))
    (inside : graphLens f g a b ⊆ interior K.footprint)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphLens f g a b))
    (w : C.Vertex Set.univ) (at_w : K.projectedVertex w ∈ graphLens f g a b)
    (initial : Bool) (at_end : K.projectedVertex w 0 = if initial then a else b)
    {u v s t : Plane} (advance_u : 0 < (if initial then u 0 else -u 0))
    (advance_v : 0 < (if initial then v 0 else -v 0))
    {D : Set ℝ}
    (on_bank : segment ℝ (K.projectedVertex w) (K.projectedVertex w + u) ⊆ graphPoint f '' D)
    (on_close : segment ℝ (K.projectedVertex w) (K.projectedVertex w + v) ⊆ graphPoint g '' D)
    (separate : ∀ x ∈ Set.Ioo a b, f x ≠ g x) (ab : a < b)
    (slopes : ∀ i j, C.vertexOfCorner Set.univ (i, j) = w → K.normalSlope i = s ∨ K.normalSlope i = t)
    (tangent : inner ℝ (s - t) u = 0)
    (local_rays : ∀ᶠ x in 𝓝 (K.projectedVertex w), x ∈ graphLens f g a b →
      x - K.projectedVertex w ∈ nonnegativeRay u ∪ nonnegativeRay v)
    (ref : Face)
    (active : ∀ (i : Face) (r : ℝ), 0 < r → orient 0 u v ≠ 0 →
      (∃ k, C.vertexOfCorner Set.univ (i, k) = w) →
      K.projectedVertex w ∈ (K.projectedTriangle i).carrier →
      K.projectedVertex w + r • v ∈ (K.projectedTriangle i).carrier →
      K.normalSlope i = K.normalSlope ref) :
    graphLensSign f g a b * K.regionalAngleExcess (K.graphLensFaces (graphLens f g a b)) w =
      (if initial then 1 else -1) * (K.sectionHeadingError ref v - K.sectionHeadingError ref u) := by
  let p := K.projectedVertex w
  have forward_data : ∃ x : ℝ, x ∈ Set.Ioo a b ∧
      x ∈ Set.uIoo (p 0) (p 0 + u 0) ∧ x ∈ Set.uIoo (p 0) (p 0 + v 0) := by
    cases initial
    · have h₀ : p 0 = b := at_end
      have hu : u 0 < 0 := neg_pos.mp advance_u
      have hv : v 0 < 0 := neg_pos.mp advance_v
      have ub : p 0 + u 0 < p 0 := by linarith only [hu]
      have vb : p 0 + v 0 < p 0 := by linarith only [hv]
      let lower := max a (max (p 0 + u 0) (p 0 + v 0))
      have below : lower < p 0 := max_lt (by rwa [h₀]) (max_lt ub vb)
      have bounds : (lower + p 0) / 2 ∈ Set.Ioo lower (p 0) := ⟨by linarith only [below],
        by linarith only [below]⟩
      refine ⟨_, ⟨(le_max_left _ _).trans_lt bounds.1, bounds.2.trans_eq h₀⟩, ?_, ?_⟩
      · rw [Set.uIoo_of_ge ub.le]
        exact ⟨((le_max_left _ _).trans (le_max_right _ _)).trans_lt bounds.1, bounds.2⟩
      · rw [Set.uIoo_of_ge vb.le]
        exact ⟨((le_max_right _ _).trans (le_max_right _ _)).trans_lt bounds.1, bounds.2⟩
    · have h₀ : p 0 = a := at_end
      have hu : 0 < u 0 := advance_u
      have hv : 0 < v 0 := advance_v
      have ub : p 0 < p 0 + u 0 := by linarith only [hu]
      have vb : p 0 < p 0 + v 0 := by linarith only [hv]
      let upper := min b (min (p 0 + u 0) (p 0 + v 0))
      have above : p 0 < upper := lt_min (by rwa [h₀]) (lt_min ub vb)
      have bounds : (p 0 + upper) / 2 ∈ Set.Ioo (p 0) upper := ⟨by linarith only [above],
        by linarith only [above]⟩
      refine ⟨_, ⟨h₀ ▸ bounds.1, bounds.2.trans_le (min_le_left _ _)⟩, ?_, ?_⟩
      · rw [Set.uIoo_of_le ub.le]
        exact ⟨bounds.1, bounds.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
      · rw [Set.uIoo_of_le vb.le]
        exact ⟨bounds.1, bounds.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨x, mid, in_u, in_v⟩ := forward_data
  have une : u 0 ≠ 0 := by cases initial <;> simpa using advance_u.ne'
  have vne : v 0 ≠ 0 := by cases initial <;> simpa using advance_v.ne'
  obtain ⟨r, _, on_f⟩ := graphPoint_eq_add_smul_of_segment on_bank une in_u
  obtain ⟨l, lp, on_g⟩ := graphPoint_eq_add_smul_of_segment on_close vne in_v
  have determinant := orient_ne_zero_of_distinct_graph_points (separate x mid) une on_f on_g
  have halfplane : (∀ x ∈ closedJordanDomain (graphLens f g a b), p 0 ≤ x 0) ∨
      (∀ x ∈ closedJordanDomain (graphLens f g a b), x 0 ≤ p 0) := by
    cases initial
    · exact Or.inr (fun x h => (closedJordanDomain_two_graphs_subset_slab jordan h).2.trans_eq at_end.symm)
    · exact Or.inl (fun x h => at_end.le.trans (closedJordanDomain_two_graphs_subset_slab jordan h).1)
  obtain ⟨i, l', lp', vertex, at_i, along, angle_error⟩ :=
    K.exists_graphLens_endpointLift jordan inside aligned w at_w slopes tangent local_rays halfplane
  have same := active i l' lp' determinant vertex at_i along
  have u_ne : u ≠ 0 := fun h => une (by rw [h]; rfl)
  have v_ne : v ≠ 0 := fun h => vne (by rw [h]; rfl)
  have angle_sign := K.signed_sectionAngle_sub_eq i u_ne v_ne
  rw [K.sectionHeadingError_eq_of_slope_eq same, K.sectionHeadingError_eq_of_slope_eq same] at angle_sign
  rw [angle_error]
  cases initial
  · rw [graphLensSign_of_backward_rays hf hg mid separate (neg_pos.mp advance_u) lp on_f on_g,
      neg_mul, angle_sign]
    simp only [Bool.false_eq_true, ite_false]
    ring
  · rw [graphLensSign_of_forward_rays hf hg mid separate advance_u lp on_f on_g, angle_sign]
    simp

end Unfoldings.ConvexRoof
