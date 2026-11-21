module

public import Unfoldings.Cap.SharpSectionFans
public import Unfoldings.Cap.DegenerateNormalCurvature
public import Unfoldings.Complex.ComplementaryLinkChains

/-! A corner incident to a crease can use the shorter of its complementary fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ w).Chain n)

private theorem short_link_projection_error_of_crease_first {a b : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) (K.projectedGermRay c.first) = 0)
    (short : (∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  apply K.abs_flat_link_projection_error_le_sharp c nonnegative small tilt c.first.val.1.1
  · apply K.slope_constant_of_crease_first_short_fan c (a := a) (b := b)
    · intro i
      exact slopes _ _ (c.point i).property
    · change inner ℝ (a - b) (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc) = 0
      rw [K.projectedIntervalRay_castSucc]
      exact tangent
    · exact short
  · exact K.projectedInterval_halfplane_of_sum_le_pi c short

/-- If a refined corner has at most two incident slopes and one of its rays
lies along their crease, its error is at most the sharp one-plane error.
For a reflex fan, its complementary fan gives the same absolute error. -/
theorem abs_link_projection_error_of_crease_first (internal : ¬ C.IsBoundaryVertex Set.univ w)
    {a b : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) (K.projectedGermRay c.first) = 0)
    (proper : K.projectedGermRay (C.linkTurn Set.univ w c.last) ≠ K.projectedGermRay c.first)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  classical
  let projected (p : C.Corner) := (K.projectedTriangle p.1).cornerAngle p.2
  let intrinsic (p : C.Corner) := (C.triangle p.1).cornerAngle p.2
  by_cases short : (∑ i, projected (c.point i).val.1) ≤ π
  · exact K.short_link_projection_error_of_crease_first c slopes tangent short nonnegative small tilt
  let S := C.linkSystem Set.univ w
  have free (p : C.LinkGerm Set.univ w) : S.mate p ≠ p := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ w).mpr ⟨p, fixed⟩)
  have open_fan : S.mate (S.turn c.last) ≠ c.first := by
    intro closed
    apply proper
    have h := congrArg K.projectedGermRay closed
    change K.projectedGermRay (C.linkMate Set.univ w (C.linkTurn Set.univ w c.last)) =
      K.projectedGermRay c.first at h
    simpa only [K.projectedGermRay_mate] using h
  obtain ⟨m, d, _, joined, closes, _⟩ :=
    S.exists_complementary_chain (C.linkSystem_connected Set.univ w) free c open_fan
  have different : d.first ≠ c.first := by
    rw [← joined]
    exact open_fan
  have zero := K.interiorCurvature_eq_zero_of_two_incidentSlopes height w a b slopes
  have total : C.totalAngle Set.univ w = 2 * π := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal] at zero
    linarith
  have projected_total := K.projectedTotalAngle_eq_two_pi w internal
  have projected_sum := C.sum_complementary_linkCornerWeight c d internal joined closes
    different projected
  have intrinsic_sum := C.sum_complementary_linkCornerWeight c d internal joined closes
    different intrinsic
  have projected_weights : C.regionalCornerSum Set.univ projected w =
      K.projectedTotalAngle Set.univ w := by
    simp [TriangleComplex.regionalCornerSum, projectedTotalAngle, projected]
  have intrinsic_weights : C.regionalCornerSum Set.univ intrinsic w = C.totalAngle Set.univ w := by
    simp [TriangleComplex.regionalCornerSum, TriangleComplex.totalAngle, intrinsic]
  rw [projected_weights, projected_total] at projected_sum
  rw [intrinsic_weights, total] at intrinsic_sum
  have reverse_short : (∑ i, projected (d.reverse.point i).val.1) ≤ π := by
    rw [C.sum_reverse_linkCornerWeight d projected]
    linarith only [projected_sum, short]
  have ray_match : K.projectedGermRay d.reverse.first = K.projectedGermRay c.first := by
    rw [d.reverse_first]
    change K.projectedGermRay (C.linkTurn Set.univ w d.last) = K.projectedGermRay c.first
    have h := congrArg K.projectedGermRay closes
    change K.projectedGermRay (C.linkMate Set.univ w (C.linkTurn Set.univ w d.last)) =
      K.projectedGermRay c.first at h
    simpa only [K.projectedGermRay_mate] using h
  have estimate := K.short_link_projection_error_of_crease_first d.reverse slopes
    (by rw [ray_match]; exact tangent) reverse_short nonnegative small tilt
  change |(∑ i, intrinsic (d.reverse.point i).val.1) -
      ∑ i, projected (d.reverse.point i).val.1| ≤ _ at estimate
  rw [C.sum_reverse_linkCornerWeight d intrinsic, C.sum_reverse_linkCornerWeight d projected]
    at estimate
  change |(∑ i, intrinsic (c.point i).val.1) - ∑ i, projected (c.point i).val.1| ≤ _
  rw [show (∑ i, intrinsic (c.point i).val.1) - ∑ i, projected (c.point i).val.1 =
      -((∑ i, intrinsic (d.point i).val.1) - ∑ i, projected (d.point i).val.1) by
    linarith only [intrinsic_sum, projected_sum], abs_neg]
  exact estimate

/-- Either incident boundary ray can be the crease ray. -/
theorem abs_link_projection_error_of_crease_ray (internal : ¬ C.IsBoundaryVertex Set.univ w)
    {a b : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) (K.projectedGermRay c.first) = 0 ∨
      inner ℝ (a - b) (K.projectedGermRay (C.linkTurn Set.univ w c.last)) = 0)
    (proper : K.projectedGermRay (C.linkTurn Set.univ w c.last) ≠ K.projectedGermRay c.first)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  rcases tangent with first | last
  · exact K.abs_link_projection_error_of_crease_first c internal slopes first proper
      height nonnegative small tilt
  have first : inner ℝ (a - b) (K.projectedGermRay c.reverse.first) = 0 := by
    rw [c.reverse_first]
    exact last
  have reversed : K.projectedGermRay (C.linkTurn Set.univ w c.reverse.last) ≠
      K.projectedGermRay c.reverse.first := by
    rw [c.reverse_first, c.reverse_last]
    change K.projectedGermRay ((C.linkSystem Set.univ w).turn
      ((C.linkSystem Set.univ w).turn c.first)) ≠ _
    rw [(C.linkSystem Set.univ w).turn_involutive]
    exact proper.symm
  have estimate := K.abs_link_projection_error_of_crease_first c.reverse internal slopes first
    reversed height nonnegative small tilt
  let intrinsic (p : C.Corner) := (C.triangle p.1).cornerAngle p.2
  let projected (p : C.Corner) := (K.projectedTriangle p.1).cornerAngle p.2
  change |(∑ i, intrinsic (c.reverse.point i).val.1) -
    ∑ i, projected (c.reverse.point i).val.1| ≤ _ at estimate
  rw [C.sum_reverse_linkCornerWeight c intrinsic, C.sum_reverse_linkCornerWeight c projected]
    at estimate
  exact estimate

end Unfoldings.ConvexCap
