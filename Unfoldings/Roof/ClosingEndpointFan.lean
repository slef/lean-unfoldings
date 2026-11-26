module

public import Unfoldings.Roof.SharpRestrictedCorners
public import Unfoldings.Geometry.ForwardRayFan

/-! A trimmed closing endpoint lies in one actual supporting plane on its lens side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real InnerProductGeometry Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem projected_link_short_of_coordinate {w : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n)
    (side : (∀ i, 0 ≤ K.projectedIntervalRay c i 0) ∨
      (∀ i, K.projectedIntervalRay c i 0 ≤ 0)) :
    (∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π := by
  let r := K.projectedIntervalRay c
  have nonzero (i : Fin (n + 1)) : orient 0 (r i.castSucc) (r i.succ) ≠ 0 := by
    dsimp only [r]
    rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero _
  have sign := interval_cone_orient_sign r nonzero (K.planar_arc_cones_disjoint c)
  have signs (i j : Fin (n + 1)) :
      0 < orient 0 (r i.castSucc) (r i.succ) * orient 0 (r j.castSucc) (r j.succ) := by
    by_cases h : 0 < orient 0 (r (0 : Fin (n + 1)).castSucc) (r (0 : Fin (n + 1)).succ)
    · exact mul_pos ((sign i).mpr h) ((sign j).mpr h)
    · exact mul_pos_of_neg_of_neg
        (lt_of_le_of_ne (le_of_not_gt (mt (sign i).mp h)) (nonzero i))
        (lt_of_le_of_ne (le_of_not_gt (mt (sign j).mp h)) (nonzero j))
  have estimate : (∑ i : Fin (n + 1), angle (r i.castSucc) (r i.succ)) ≤ π := by
    rcases side with positive | negative
    · exact sum_forward_ray_angles_le_pi r (K.projectedIntervalRay_ne_zero c) nonzero signs positive
    · have reflection (x y : Plane) : orient 0 (-x) (-y) = orient 0 x y := by
        simp only [orient, PiLp.zero_apply, PiLp.neg_apply, sub_zero, neg_mul_neg]
      have reversed := sum_forward_ray_angles_le_pi (fun i => -r i)
        (fun i => neg_ne_zero.mpr (K.projectedIntervalRay_ne_zero c i))
        (fun i => by simpa only [reflection] using nonzero i)
        (fun i j => by simpa only [reflection] using signs i j)
        (fun i => by simpa only [PiLp.neg_apply, neg_nonneg] using negative i)
      simpa only [angle_neg_neg] using reversed
  simpa only [r, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_angle] using estimate

open Classical in
/-- At a forward or backward endpoint lens the actual restricted angle error
is the signed difference of ordinary angles in the plane incident to its
closing ray. The other ray follows the old crease. -/
theorem restrictedEndpointTurnError_eq_angle_of_crease (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (closingFirst : Bool)
    {s t : Plane}
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope f = s ∨ K.normalSlope f = t)
    (side : (∀ g : C.LinkGerm Set.univ (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)),
        g.val.1.1 ∈ U → 0 ≤ K.projectedGermRay g 0) ∨
      (∀ g : C.LinkGerm Set.univ (C.includeRestrictedVertexUniv U
        ((C.restrictFaces U).boundaryEndVertex Set.univ p)),
          g.val.1.1 ∈ U → K.projectedGermRay g 0 ≤ 0))
    (tangent : inner ℝ (s - t) (Cap.horizontal ((K.folding.restrictFaces U).germDirection
      (if closingFirst then ((C.restrictFaces U).boundaryMate Set.univ p).val else p.val))) = 0) :
    let R := C.restrictFaces U
    let F := K.folding.restrictFaces U
    let q := R.boundaryMate Set.univ p
    let f := if closingFirst then p.val.1.1.val else q.val.1.1.val
    let a := Cap.horizontal (F.germDirection p.val)
    let b := Cap.horizontal (F.germDirection q.val)
    (-K.restrictedBoundaryTurnError U p) =
      angle (K.sectionDirection f a) (K.sectionDirection f b) - angle a b := by
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  obtain ⟨n, c, first, last, first_face, last_face, member, exact_turn⟩ :=
    K.exists_restricted_link_with_signed_projection_error U p
  let ray := K.projectedIntervalRay c
  have side' : (∀ i, 0 ≤ ray i 0) ∨ (∀ i, ray i 0 ≤ 0) := by
    have apply_universal (P : Plane → Prop)
        (h : ∀ g : C.LinkGerm Set.univ (C.includeRestrictedVertexUniv U
          (R.boundaryEndVertex Set.univ p)), g.val.1.1 ∈ U → P (K.projectedGermRay g)) :
        ∀ i, P (ray i) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [show ray (Fin.last (n + 1)) = _ from K.projectedIntervalRay_last c]
        exact h _ (member (Fin.last n))
      · rw [show ray j.castSucc = _ from K.projectedIntervalRay_castSucc c j]
        exact h _ (member j)
    exact side.imp (apply_universal (fun p => 0 ≤ p 0)) (apply_universal (fun p => p 0 ≤ 0))
  have short := K.projected_link_short_of_coordinate c side'
  have halfplane := K.projectedInterval_halfplane_of_sum_le_pi c short
  have at₀ : K.projectedIntervalRay c 0 = Cap.horizontal (F.germDirection p.val) := by
    change ray (0 : Fin (n + 1)).castSucc = _
    rw [show ray (0 : Fin (n + 1)).castSucc = _ from K.projectedIntervalRay_castSucc c 0]
    exact first
  have at₁ : K.projectedIntervalRay c (Fin.last (n + 1)) = Cap.horizontal (F.germDirection q.val) :=
    (K.projectedIntervalRay_last c).trans last
  have projected := K.sum_projected_link_corner_angles c halfplane
  rw [at₀, at₁] at projected
  have s' (i : Fin (n + 1)) : K.normalSlope (c.point i).val.1.1 = s ∨
      K.normalSlope (c.point i).val.1.1 = t := slopes _ _ (c.point i).property
  cases closingFirst
  · have initial : inner ℝ (s - t) (ray 0) = 0 := by dsimp [ray]; rw [at₀]; exact tangent
    have constant := K.slope_constant_of_crease_first_short_fan c s' initial short
    have to_closure (i : Fin (n + 1)) :
        K.normalSlope (c.point i).val.1.1 = K.normalSlope q.val.1.1.val := by
      rw [← last_face]
      exact (constant i).trans (constant (Fin.last n)).symm
    have intrinsic := K.sum_flat_link_corner_angles c q.val.1.1.val to_closure halfplane
    rw [at₀, at₁] at intrinsic
    rw [exact_turn, intrinsic, projected]
    rfl
  · let d := c.reverse
    let intrinsic (p : C.Corner) := (C.triangle p.1).cornerAngle p.2
    let projectedCorner (p : C.Corner) := (K.projectedTriangle p.1).cornerAngle p.2
    have short' : (∑ i, projectedCorner (d.point i).val.1) ≤ π := by
      dsimp only [d]
      rw [C.sum_reverse_linkCornerWeight c projectedCorner]
      exact short
    have at_first : K.projectedIntervalRay d 0 = Cap.horizontal (F.germDirection q.val) := by
      change K.projectedIntervalRay d (0 : Fin (n + 1)).castSucc = _
      rw [K.projectedIntervalRay_castSucc]
      change K.projectedGermRay c.reverse.first = _
      rw [c.reverse_first]
      exact last
    have at_last : K.projectedIntervalRay d (Fin.last (n + 1)) = Cap.horizontal (F.germDirection p.val) := by
      rw [K.projectedIntervalRay_last]
      change K.projectedGermRay ((C.linkSystem Set.univ _).turn c.reverse.last) = _
      rw [c.reverse_last, (C.linkSystem Set.univ _).turn_involutive]
      exact first
    have init : inner ℝ (s - t) (K.projectedIntervalRay d 0) = 0 := by
      rw [at_first]
      exact tangent
    have s'' (i : Fin (n + 1)) : K.normalSlope (d.point i).val.1.1 = s ∨
        K.normalSlope (d.point i).val.1.1 = t := slopes _ _ (d.point i).property
    have constant := K.slope_constant_of_crease_first_short_fan d s'' init short'
    have face_eq : d.last.val.1.1 = p.val.1.1.val := by
      change c.reverse.last.val.1.1 = p.val.1.1.val
      rw [c.reverse_last]
      exact first_face
    have to_closure (i : Fin (n + 1)) :
        K.normalSlope (d.point i).val.1.1 = K.normalSlope p.val.1.1.val := by
      rw [← face_eq]
      exact (constant i).trans (constant (Fin.last n)).symm
    have i_angles := K.sum_flat_link_corner_angles d p.val.1.1.val to_closure
      (K.projectedInterval_halfplane_of_sum_le_pi d short')
    rw [at_first, at_last] at i_angles
    change (∑ i, intrinsic (c.reverse.point i).val.1) =
      angle (K.sectionDirection p.val.1.1.val (Cap.horizontal (F.germDirection q.val)))
        (K.sectionDirection p.val.1.1.val (Cap.horizontal (F.germDirection p.val))) at i_angles
    rw [C.sum_reverse_linkCornerWeight c intrinsic, angle_comm] at i_angles
    rw [exact_turn, i_angles, projected]
    rfl

end Unfoldings.ConvexRoof
