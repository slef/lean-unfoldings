module

public import Unfoldings.Cap.JordanBankPositions
public import Unfoldings.Cap.JordanLocalTwoRays
public import Unfoldings.Cap.SharpRestrictedCorners

/-! Sharp local corner errors on an actual Jordan contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- A Jordan corner with at most two supporting slopes and one tangent ray
has the sharp one-plane turn error, including a reflex corner. -/
theorem abs_jordan_turn_error_le_sharp_of_crease_ray
    (inside : J ⊆ interior K.footprint)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    {a b : Plane}
    (slopes : ∀ f k, C.vertexOfCorner Set.univ (f, k) =
      ((K.jordanContourVertexEquiv jordan contains avoids) i).val →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    let U := K.jordanFaces J
    let p := (K.jordanContour jordan contains avoids).cycle.point i
    let q := (C.restrictFaces U).boundaryMate Set.univ p
    let u := Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val)
    let v := Cap.horizontal ((K.folding.restrictFaces U).germDirection q.val)
    (inner ℝ (a - b) u = 0 ∨ inner ℝ (a - b) v = 0) →
    |K.jordanContourTurnError jordan contains avoids i| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  dsimp only
  intro tangent
  have internal : ¬ C.IsBoundaryVertex Set.univ
      ((K.jordanContourVertexEquiv jordan contains avoids) i).val := by
    apply (K.projectedVertex_mem_interior_iff _).mp
    exact inside ((K.jordanContourVertexEquiv jordan contains avoids) i).property
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
  have nonzero : Cap.horizontal (F.germDirection p.val) ≠ 0 := by
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    exact ray
  have different : Cap.horizontal (F.germDirection (R.boundaryMate Set.univ p).val) ≠
      Cap.horizontal (F.germDirection p.val) := by
    intro same
    have h := K.restricted_boundary_rays_angle_ne_zero U p
    change InnerProductGeometry.angle (Cap.horizontal (F.germDirection p.val))
      (Cap.horizontal (F.germDirection (R.boundaryMate Set.univ p).val)) ≠ 0 at h
    rw [same, InnerProductGeometry.angle_self nonzero] at h
    exact h rfl
  exact K.abs_restrictedBoundaryTurnError_le_sharp_of_crease_ray U p internal slopes tangent
    different height nonnegative small tilt

include jordan contains avoids in
open Classical in
/-- Local geometric rays can certify the sharp corner bound without choosing
which of the two intrinsic boundary ends starts the fan. -/
theorem abs_jordan_turn_error_le_sharp_of_local_crease_ray
    (inside : J ⊆ interior K.footprint)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    {a b crease closing : Plane}
    (slopes : ∀ f k, C.vertexOfCorner Set.univ (f, k) =
      ((K.jordanContourVertexEquiv jordan contains avoids) i).val →
      K.normalSlope f = a ∨ K.normalSlope f = b)
    (tangent : inner ℝ (a - b) crease = 0)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    (locally : ∀ᶠ x in 𝓝 (K.jordanBankPosition jordan contains avoids i),
      x ∈ J → x - K.jordanBankPosition jordan contains avoids i ∈
        nonnegativeRay crease ∪ nonnegativeRay closing)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |K.jordanContourTurnError jordan contains avoids i| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  let q := R.boundaryMate Set.univ p
  have other : ∀ᶠ x in 𝓝 (Cap.horizontal (F.boundaryPosition q)),
      x ∈ J → x - Cap.horizontal (F.boundaryPosition q) ∈
        nonnegativeRay crease ∪ nonnegativeRay closing := by
    rw [F.boundaryPosition_mate p]
    exact locally
  have rays_first := K.jordan_bank_direction_of_local_two_rays jordan contains avoids p
    crease closing locally
  have rays_last := K.jordan_bank_direction_of_local_two_rays jordan contains avoids q
    crease closing other
  apply K.abs_jordan_turn_error_le_sharp_of_crease_ray jordan contains avoids inside i
    slopes height nonnegative small tilt
  change inner ℝ (a - b) (Cap.horizontal (F.germDirection p.val)) = 0 ∨
    inner ℝ (a - b) (Cap.horizontal (F.germDirection q.val)) = 0
  rcases rays_first with ⟨s, _, same⟩ | ⟨s, sp, same⟩
  · exact Or.inl (by rw [same, real_inner_smul_right, tangent, mul_zero])
  rcases rays_last with ⟨t, _, opposite⟩ | ⟨t, tp, opposite⟩
  · exact Or.inr (by rw [opposite, real_inner_smul_right, tangent, mul_zero])
  exfalso
  have genuine : closing ≠ 0 := by
    intro zero
    let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    apply ray
    change Cap.horizontal (F.germDirection p.val) = 0
    rw [same, zero, smul_zero]
  have h := K.restricted_boundary_rays_angle_ne_zero U p
  change InnerProductGeometry.angle (Cap.horizontal (F.germDirection p.val))
    (Cap.horizontal (F.germDirection q.val)) ≠ 0 at h
  rw [same, opposite, InnerProductGeometry.angle_smul_left_of_pos _ _ sp,
    InnerProductGeometry.angle_smul_right_of_pos _ _ tp, InnerProductGeometry.angle_self genuine] at h
  exact h rfl


end Unfoldings.ConvexCap
