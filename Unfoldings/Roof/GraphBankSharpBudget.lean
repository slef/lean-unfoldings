module

public import Unfoldings.Roof.ClosingGraphTurnBudget
public import Unfoldings.Roof.GraphRegionBalance

/-! The two endpoint lenses and the regular closing graph bound the fixed bank's heading. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The signed angle excess of the chosen bank between two trimmed ends. -/
def graphBankAngleSum (f : ℝ → ℝ) (sample : Face → Plane) (a b : ℝ) (right : Bool) : ℝ := by
  classical
  exact ∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ graphPoint f '' Set.Ioo a b then
    K.regionalAngleExcess (facesAboveGraph sample f a b) w +
      (if right then C.interiorAngularDefect Set.univ w else 0) else 0

open Classical in
set_option maxHeartbeats 1500000 in
/-- The fixed graph bank pays just two endpoint errors, the connector's total
error, and the actual intrinsic curvature of the roof. -/
theorem abs_graphBankAngleSum_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (order : a < b) (start : f a = g a) (finish : f b = g b)
    (finite : {t ∈ Set.Icc a b | f t = g t}.Finite)
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
    (aligned_f : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))
    (aligned_g : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint g '' Set.Icc a b))
    (contained : (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) ⊆ interior K.footprint)
    (flat_g : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b →
      C.interiorAngularDefect Set.univ w = 0)
    (left right : C.Vertex Set.univ)
    (at_left : K.projectedVertex left = graphPoint f a) (at_right : K.projectedVertex right = graphPoint f b)
    {u₁ u₂ v₁ v₂ s₁ s₂ t₁ t₂ : Plane}
    (slopes_left : ∀ j i, C.vertexOfCorner Set.univ (j, i) = left →
      K.normalSlope j = s₁ ∨ K.normalSlope j = s₂)
    (slopes_right : ∀ j i, C.vertexOfCorner Set.univ (j, i) = right →
      K.normalSlope j = t₁ ∨ K.normalSlope j = t₂)
    (tangent_left : inner ℝ (s₁ - s₂) u₁ = 0) (tangent_right : inner ℝ (t₁ - t₂) v₁ = 0)
    (rays_left : ∀ᶠ x in 𝓝 (K.projectedVertex left),
      x ∈ (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) →
        x - K.projectedVertex left ∈ nonnegativeRay u₁ ∪ nonnegativeRay u₂)
    (rays_right : ∀ᶠ x in 𝓝 (K.projectedVertex right),
      x ∈ (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) →
        x - K.projectedVertex right ∈ nonnegativeRay v₁ ∪ nonnegativeRay v₂)
    {φ expense : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (closing : |∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b then
      K.regionalAngleExcess (facesAboveGraph sample g a b) w else 0| ≤ expense)
    (right_bank : Bool) :
    |K.graphBankAngleSum f sample a b right_bank| ≤
      C.totalInteriorAngularDefect Set.univ + 2 * (2 * arcsin (tan (φ / 2) ^ 2)) + expense := by
  obtain ⟨n, c, first, last, crossing, jordan, disjoint, avoids⟩ :=
    exists_ordered_graphLenses f g hf hg order start finish finite
  let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
  let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
  let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
  let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
  let δ := 2 * arcsin (tan (φ / 2) ^ 2)
  have included (i : Fin (n + 1)) : J i ⊆ curve := by
    have bounded : Set.Icc (c i.castSucc) (c i.succ) ⊆ Set.Icc a b := by
      rw [← first, ← last]
      exact Set.Icc_subset_Icc (c.monotone (Fin.zero_le _)) (c.monotone (Fin.le_last _))
    exact Set.union_subset_union (Set.image_mono bounded) (Set.image_mono bounded)
  have aligned (i : Fin (n + 1)) j : Disjoint (interior (K.projectedTriangle j).carrier) (J i) :=
    ((aligned_f j).union_right (aligned_g j)).mono_right (included i)
  have sample_off (j : Face) (window : sample j 0 ∈ Set.Ioo a b) :
      sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0) := by
    have on_graph (h : ℝ → ℝ) (eq : sample j 1 = h (sample j 0)) :
        sample j ∈ graphPoint h '' Set.Icc a b := by
      refine ⟨sample j 0, Set.Ioo_subset_Icc_self window, ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact eq.symm
    exact ⟨fun eq => Set.disjoint_left.mp (aligned_f j) (sample_in j) (on_graph f eq),
      fun eq => Set.disjoint_left.mp (aligned_g j) (sample_in j) (on_graph g eq)⟩
  let first_i : Fin (n + 1) := 0
  let last_i : Fin (n + 1) := Fin.last n
  have at_initial : K.projectedVertex left ∈ J first_i :=
    Or.inl ⟨a, ⟨by rw [show c first_i.castSucc = a from first],
      first.ge.trans (c.monotone (Fin.zero_le _))⟩, at_left.symm⟩
  have at_terminal : K.projectedVertex right ∈ J last_i :=
    Or.inl ⟨b, ⟨(c.monotone (Fin.le_last _)).trans last.le,
      by change b ≤ c (Fin.last n).succ; rw [Fin.succ_last, last]⟩, at_right.symm⟩
  have left_bound : |F left - G left| ≤ δ := by
    rw [show |F left - G left| = |K.regionalAngleExcess (K.graphLensFaces (J first_i)) left| from
      K.abs_graph_regionDifference_eq_firstLens hf hg c first last crossing jordan aligned sample
        sample_in sample_off left (congrArg (fun p : Plane => p 0) at_left)]
    exact K.abs_graphLens_regionalAngleExcess_le_sharp_of_crease_ray
      (jordan first_i) ((included first_i).trans contained) (aligned first_i) left at_initial
      slopes_left tangent_left (rays_left.mono (fun _ at_ray hit => at_ray (included first_i hit)))
      nonnegative small tilt
  have right_bound : |F right - G right| ≤ δ := by
    rw [show |F right - G right| = |K.regionalAngleExcess (K.graphLensFaces (J last_i)) right| from
      K.abs_graph_regionDifference_eq_lastLens hf hg c first last crossing jordan aligned sample
        sample_in sample_off right (congrArg (fun p : Plane => p 0) at_right)]
    exact K.abs_graphLens_regionalAngleExcess_le_sharp_of_crease_ray
      (jordan last_i) ((included last_i).trans contained) (aligned last_i) right at_terminal
      slopes_right tangent_right (rays_right.mono (fun _ at_ray hit => at_ray (included last_i hit)))
      nonnegative small tilt
  let A := K.graphBankAngleSum f sample a b right_bank
  let B := ∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b then G w else 0
  let D := ∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ curve ∧
    K.projectedVertex w 0 ∉ Set.Ioo a b then F w - G w else 0
  have balance : |A - B + D| ≤ C.totalInteriorAngularDefect Set.univ :=
    K.abs_graph_boundaryAngleBalance_le hf hg c first last crossing sample sample_in endpoints
      aligned_f aligned_g flat_g right_bank contained jordan included
      (fun i => (avoids i).mono_right (Set.union_subset_union
        (Set.image_subset_range _ _) (Set.image_subset_range _ _))) disjoint
  have ends : |D| ≤ 2 * δ :=
    K.abs_graph_endpoint_sum_le sample order start finish left right at_left at_right left_bound right_bound
  have loop : A = (A - B + D) + B - D := by ring
  change |A| ≤ _
  rw [loop, sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  exact (by
    have accumulated := add_le_add (abs_add_le (A - B + D) B) (le_refl |D|)
    exact accumulated.trans (by
      change |B| ≤ expense at closing
      linarith only [balance, closing, ends]))

end Unfoldings.ConvexRoof
