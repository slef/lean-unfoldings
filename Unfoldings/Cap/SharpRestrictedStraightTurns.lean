module

public import Unfoldings.Cap.SharpStraightLink
public import Unfoldings.Cap.RestrictedSectionSum

/-! The sharp local turn estimate on the actual boundary of a restricted cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- A regular straight contact pays only the sine-scaled change of the two
actual support inclinations. The selected link and its boundary directions
come from the given restricted complex. -/
theorem abs_restrictedBoundaryTurnError_le_sin_mul_active_angle {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (d s₁ s₂ : Plane)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope f = s₁ ∨ K.normalSlope f = s₂)
    (transverse : s₁ = s₂ ∨ inner ℝ (s₁ - s₂) d ≠ 0)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (first : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • d)
    (last : Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ p).val) = b • (-d)) :
    |K.restrictedBoundaryTurnError U p| ≤ sin φ *
      angle (K.spatialDirection p.val.1.1.val d)
        (K.spatialDirection ((C.restrictFaces U).boundaryMate Set.univ p).val.1.1.val d) := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  obtain ⟨n, chain, first_chain, last_chain, covers⟩ := R.exists_boundary_link Set.univ p
  let c := C.includeRestrictedLinkChain U chain
  have head : K.projectedIntervalRay c 0 = a • d := by
    change K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    have h := (K.horizontal_germDirection (C.includeRestrictedLinkGerm U chain.first)).symm
    change K.projectedGermRay (C.includeRestrictedLinkGerm U chain.first) =
      Cap.horizontal (F.germDirection chain.first.val) at h
    rw [first_chain] at h
    exact h.trans first
  have tail : K.projectedIntervalRay c (Fin.last (n + 1)) = b • (-d) := by
    rw [K.projectedIntervalRay_last]
    have h := (K.horizontal_germDirection
      (C.includeRestrictedLinkGerm U (R.linkTurn Set.univ w chain.last))).symm
    change K.projectedGermRay (C.includeRestrictedLinkGerm U (R.linkTurn Set.univ w chain.last)) =
      Cap.horizontal (F.germDirection (R.linkTurn Set.univ w chain.last).val) at h
    rw [last_chain] at h
    exact h.trans last
  have genuine : d ≠ 0 := by
    intro zero
    exact K.projectedIntervalRay_ne_zero c 0 (by rw [head, zero, smul_zero])
  have straight : angle (Cap.horizontal (F.germDirection p.val))
      (Cap.horizontal (F.germDirection q.val)) = π := by
    rw [first, last, angle_smul_left_of_pos _ _ a_pos,
      angle_smul_right_of_pos _ _ b_pos, angle_neg_right, angle_self genuine, sub_zero]
  have projected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w chain covers
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  have flat := K.restricted_projected_angle_eq_pi U p internal straight
  have intrinsic : (∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.totalAngle Set.univ w := R.sum_linkCornerAngle Set.univ w chain covers
  have faces (i : Fin (n + 1)) : K.normalSlope (c.point i).val.1.1 = s₁ ∨
      K.normalSlope (c.point i).val.1.1 = s₂ :=
    slopes (c.point i).val.1.1 (c.point i).val.1.2 (c.point i).property
  have bnd := K.abs_straight_link_turn_le_sin_tilt nonnegative small tilt c d s₁ s₂ faces
    transverse a_pos b_pos head tail (projected.trans flat)
  have a_face : c.first.val.1.1 = p.val.1.1.val := by
    exact congrArg (fun g : R.Germ => g.1.1.val) first_chain
  have b_face : c.last.val.1.1 = q.val.1.1.val := by
    change (R.linkTurn Set.univ w chain.last).val.1.1.val = q.val.1.1.val
    exact congrArg (fun g : R.Germ => g.1.1.val) last_chain
  rw [intrinsic, a_face, b_face] at bnd
  change |(π - R.totalAngle Set.univ w) -
      (π - R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle
        c.2) w)| ≤ _
  rwa [flat, sub_self, sub_zero]

end Unfoldings.ConvexCap
