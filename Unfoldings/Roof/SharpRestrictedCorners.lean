module

public import Unfoldings.Roof.SharpRestrictedSection
public import Unfoldings.Roof.CurvatureNormalInterior
public import Unfoldings.Geometry.SegmentVertices
public import Unfoldings.Complex.ComplementaryLinkChains

/-! A corner incident to a crease can use the shorter of its complementary fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {w : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ w).Chain n)

/-- A reflex fan at a flat vertex has a short complementary fan with the
same two oriented boundary rays and the same absolute projection error. -/
theorem exists_short_link_same_projection_error
    (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (total : C.totalAngle Set.univ w = 2 * π)
    (proper : K.projectedGermRay (C.linkTurn Set.univ w c.last) ≠ K.projectedGermRay c.first)
    (long : π < ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) :
    ∃ (m : ℕ) (d : (C.linkSystem Set.univ w).Chain m),
      (∑ i, (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) ≤ π ∧
      K.projectedGermRay d.first = K.projectedGermRay c.first ∧
      K.projectedGermRay (C.linkTurn Set.univ w d.last) =
        K.projectedGermRay (C.linkTurn Set.univ w c.last) ∧
      |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
        ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2| =
      |(∑ i, (C.triangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) -
        ∑ i, (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2| := by
  classical
  let projected (p : C.Corner) := (K.projectedTriangle p.1).cornerAngle p.2
  let intrinsic (p : C.Corner) := (C.triangle p.1).cornerAngle p.2
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
    linarith only [projected_sum, long]
  have ray_match : K.projectedGermRay d.reverse.first = K.projectedGermRay c.first := by
    rw [d.reverse_first]
    change K.projectedGermRay (C.linkTurn Set.univ w d.last) = K.projectedGermRay c.first
    have h := congrArg K.projectedGermRay closes
    change K.projectedGermRay (C.linkMate Set.univ w (C.linkTurn Set.univ w d.last)) =
      K.projectedGermRay c.first at h
    simpa only [K.projectedGermRay_mate] using h
  have last_match : K.projectedGermRay (S.turn d.reverse.last) =
      K.projectedGermRay (S.turn c.last) := by
    rw [d.reverse_last, S.turn_involutive, ← joined]
    exact K.projectedGermRay_mate _
  refine ⟨m, d.reverse, reverse_short, ray_match, last_match, ?_⟩
  change |(∑ i, intrinsic (c.point i).val.1) - ∑ i, projected (c.point i).val.1| =
    |(∑ i, intrinsic (d.reverse.point i).val.1) - ∑ i, projected (d.reverse.point i).val.1|
  rw [C.sum_reverse_linkCornerWeight d intrinsic, C.sum_reverse_linkCornerWeight d projected,
    show (∑ i, intrinsic (c.point i).val.1) - ∑ i, projected (c.point i).val.1 =
      -((∑ i, intrinsic (d.point i).val.1) - ∑ i, projected (d.point i).val.1) by
    linarith only [intrinsic_sum, projected_sum], abs_neg]

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
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  by_cases short : (∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π
  · exact K.short_link_projection_error_of_crease_first c slopes tangent short nonnegative small tilt
  have incident : K.incidentSlopes w ⊆ segment ℝ a b := by
    rintro x ⟨f, i, contact, rfl⟩
    rcases slopes f i contact with left | right
    · rw [left]; exact left_mem_segment ℝ _ _
    · rw [right]; exact right_mem_segment ℝ _ _
  have zero := K.interiorCurvature_eq_zero_of_normalPolygon_collinear w
    ((collinear_segment a b).subset (convexHull_min incident (convex_segment a b)))
  have total : C.totalAngle Set.univ w = 2 * π := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal] at zero
    linarith
  obtain ⟨m, d, short_d, first_d, _, equal⟩ :=
    K.exists_short_link_same_projection_error c internal total proper (lt_of_not_ge short)
  rw [equal]
  exact K.short_link_projection_error_of_crease_first d slopes
    (by rw [first_d]; exact tangent) short_d nonnegative small tilt

/-- Either incident boundary ray can be the crease ray. -/
theorem abs_link_projection_error_of_crease_ray (internal : ¬ C.IsBoundaryVertex Set.univ w)
    {a b : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) = w →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) (K.projectedGermRay c.first) = 0 ∨
      inner ℝ (a - b) (K.projectedGermRay (C.linkTurn Set.univ w c.last)) = 0)
    (proper : K.projectedGermRay (C.linkTurn Set.univ w c.last) ≠ K.projectedGermRay c.first)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  rcases tangent with first | last
  · exact K.abs_link_projection_error_of_crease_first c internal slopes first proper
      nonnegative small tilt
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
    reversed nonnegative small tilt
  let intrinsic (p : C.Corner) := (C.triangle p.1).cornerAngle p.2
  let projected (p : C.Corner) := (K.projectedTriangle p.1).cornerAngle p.2
  change |(∑ i, intrinsic (c.reverse.point i).val.1) -
    ∑ i, projected (c.reverse.point i).val.1| ≤ _ at estimate
  rw [C.sum_reverse_linkCornerWeight c intrinsic, C.sum_reverse_linkCornerWeight c projected]
    at estimate
  exact estimate

section Restricted

open Classical in
/-- The literal restricted corner reads the same rays and angle difference
and signed angle difference as its included interval in the full roof link. -/
theorem exists_restricted_link_with_signed_projection_error (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    let R := C.restrictFaces U
    let w := C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ p)
    let F := K.folding.restrictFaces U
    ∃ (n : ℕ) (c : (C.linkSystem Set.univ w).Chain n),
      K.projectedGermRay c.first = Cap.horizontal (F.germDirection p.val) ∧
      K.projectedGermRay (C.linkTurn Set.univ w c.last) =
        Cap.horizontal (F.germDirection (R.boundaryMate Set.univ p).val) ∧
      c.first.val.1.1 = p.val.1.1.val ∧
      c.last.val.1.1 = (R.boundaryMate Set.univ p).val.1.1.val ∧
      (∀ i, (c.point i).val.1.1 ∈ U) ∧
      -K.restrictedBoundaryTurnError U p =
        (∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
          ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2 := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  obtain ⟨n, chain, first_chain, last_chain, covers⟩ := R.exists_boundary_link Set.univ p
  let c := C.includeRestrictedLinkChain U chain
  have first_ray : K.projectedGermRay c.first = Cap.horizontal (F.germDirection p.val) := by
    change K.projectedGermRay (C.includeRestrictedLinkGerm U chain.first) = _
    rw [← K.horizontal_germDirection]
    change Cap.horizontal (F.germDirection chain.first.val) = _
    rw [first_chain]
  have last_ray : K.projectedGermRay (C.linkTurn Set.univ
      (C.includeRestrictedVertexUniv U w) c.last) = Cap.horizontal (F.germDirection q.val) := by
    have h := (K.horizontal_germDirection (C.includeRestrictedLinkGerm U
      (R.linkTurn Set.univ w chain.last))).symm
    change K.projectedGermRay (C.includeRestrictedLinkGerm U (R.linkTurn Set.univ w chain.last)) =
      Cap.horizontal (F.germDirection (R.linkTurn Set.univ w chain.last).val) at h
    rw [last_chain] at h
    exact h
  have first_face : c.first.val.1.1 = p.val.1.1.val :=
    congrArg (fun g : R.Germ => g.1.1.val) first_chain
  have last_face : c.last.val.1.1 = q.val.1.1.val := by
    change (R.linkTurn Set.univ w chain.last).val.1.1.val = q.val.1.1.val
    exact congrArg (fun g : R.Germ => g.1.1.val) last_chain
  refine ⟨n, c, first_ray, last_ray, first_face, last_face,
    fun i => (chain.point i).val.1.1.property, ?_⟩
  have projected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w chain covers (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  have intrinsic : (∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.totalAngle Set.univ w :=
    R.sum_linkCornerAngle Set.univ w chain covers
  rw [intrinsic, projected]
  change -((π - R.totalAngle Set.univ w) - (π -
    R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)) = _
  ring

open Classical in
/-- The literal restricted corner reads the same rays and angle difference
as its included interval in the full roof link. -/
theorem exists_restricted_link_with_projection_error (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    let R := C.restrictFaces U
    let w := C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ p)
    let F := K.folding.restrictFaces U
    ∃ (n : ℕ) (c : (C.linkSystem Set.univ w).Chain n),
      K.projectedGermRay c.first = Cap.horizontal (F.germDirection p.val) ∧
      K.projectedGermRay (C.linkTurn Set.univ w c.last) =
        Cap.horizontal (F.germDirection (R.boundaryMate Set.univ p).val) ∧
      |K.restrictedBoundaryTurnError U p| =
        |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
          ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2| := by
  obtain ⟨n, c, first, last, _, _, _, exact⟩ :=
    K.exists_restricted_link_with_signed_projection_error U p
  exact ⟨n, c, first, last, (abs_neg _).symm.trans (congrArg abs exact)⟩

open Classical in
/-- The literal corner of a restricted bank satisfies the sharp estimate
when either of its rays follows the crease of its two support slopes. -/
theorem abs_restrictedBoundaryTurnError_le_sharp_of_crease_ray (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    {a b : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent :
      inner ℝ (a - b) (Cap.horizontal
        ((K.folding.restrictFaces U).germDirection p.val)) = 0 ∨
      inner ℝ (a - b) (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) = 0)
    (different : Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val) ≠
      Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |K.restrictedBoundaryTurnError U p| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  obtain ⟨n, c, first_ray, last_ray, error⟩ := K.exists_restricted_link_with_projection_error U p
  rw [error]
  exact K.abs_link_projection_error_of_crease_ray c internal slopes
    (by rwa [first_ray, last_ray]) (by rwa [first_ray, last_ray]) nonnegative small tilt


end Restricted

end Unfoldings.ConvexRoof
