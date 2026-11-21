module

public import Unfoldings.Roof.AdaptiveCommonForest
public import Unfoldings.Roof.CompatiblePotentialPaths

/-! Histories in the common-potential cut construction retain their adaptive length bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatibleAdaptiveRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {L : Set Plane} {r margin η : ℝ} (R : K.CompatibleAdaptiveRouting U G boundary L r margin η)

private theorem affine_segment_along (x d : Plane) (s t a : ℝ) :
    AffineMap.lineMap (x + s • d) (x + t • d) a = x + (s + (t - s) * a) • d := by
  rw [AffineMap.lineMap_apply_module']
  module

/-- Partial segments of any adaptive step keep the same routing witness. -/
theorem followsStep_subsegment {x y : Plane} (follows : R.FollowsStep x y)
    {a b : ℝ} (first : 0 ≤ a) (ordered : a ≤ b) (last : b ≤ 1) :
    R.FollowsStep (AffineMap.lineMap x y a) (AffineMap.lineMap x y b) := by
  have between {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s ≤ t) :
      0 ≤ s + (t - s) * a ∧ s + (t - s) * a ≤ s + (t - s) * b ∧
        s + (t - s) * b ≤ t := by
    have weight := sub_nonneg.mpr forward
    exact ⟨add_nonneg nonnegative (mul_nonneg weight first),
      add_le_add_right (mul_le_mul_of_nonneg_left ordered weight) s, by
        linarith only [mul_le_mul_of_nonneg_left last weight]⟩
  rcases follows with ⟨v, s, t, nonnegative, forward, stop, rfl, rfl⟩ |
    ⟨v, s, t, nonnegative, forward, rfl, rfl⟩
  · obtain ⟨start, ordered, last⟩ := between nonnegative forward
    exact Or.inl ⟨v, s + (t - s) * a, s + (t - s) * b, start, ordered,
      last.trans stop, affine_segment_along _ _ _ _ _, affine_segment_along _ _ _ _ _⟩
  · obtain ⟨start, ordered, _⟩ := between nonnegative forward
    exact Or.inr ⟨v, s + (t - s) * a, s + (t - s) * b, start, ordered,
      affine_segment_along _ _ _ _ _, affine_segment_along _ _ _ _ _⟩

/-- The description used to construct the cut mesh gives no new paths. Each
of its partial links belongs to the identical adaptive history relation. -/
theorem followsStep_of_common (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    {x y : Plane}
    (step : (R.asCommonPotentialRouting positive disk bound_pos ratio upper).FollowsStep x y) : R.FollowsStep x y := by
  let common := R.asCommonPotentialRouting positive disk bound_pos ratio upper
  change common.FollowsStep x y at step
  rcases step with ⟨v, s, t, first, ordered, last, hx, hy⟩ |
    ⟨v, s, t, first, ordered, hx, hy⟩
  · let a := K.projectedVertex v.val
    let b := K.projectedVertex (R.parents.parent v.val)
    change x = a + s • (b - a) at hx
    change y = a + t • (b - a) at hy
    have x_eq : AffineMap.lineMap a b s = x := by
      rw [hx, AffineMap.lineMap_apply_module', add_comm]
    have y_eq : AffineMap.lineMap a b t = y := by
      rw [hy, AffineMap.lineMap_apply_module', add_comm]
    have full : R.FollowsStep a b := R.parent_followsStep v.property
    have restricted := R.followsStep_subsegment full first ordered last
    rwa [x_eq, y_eq] at restricted
  · exact Or.inr ⟨common.terminalIndex v, s, t, first, ordered, hx, hy⟩

/-- Every ordered bank obtained from the common cut construction retains
the adaptive radius-to-inradius length estimate. -/
theorem commonFollows_length_bound (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    {n : ℕ} (P : PolygonalChain Plane n)
    (follows : (R.asCommonPotentialRouting positive disk bound_pos ratio upper).Follows P) :
    P.projectedLength ≤ (b / r) * ‖P.vertex (Fin.last n) - P.vertex 0‖ :=
  R.follows_length_bound positive disk upper P (fun i =>
    R.followsStep_of_common positive disk bound_pos ratio upper (follows i))

end Unfoldings.ConvexRoof.CompatibleAdaptiveRouting
