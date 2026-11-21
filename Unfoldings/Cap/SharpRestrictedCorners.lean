module

public import Unfoldings.Cap.SharpCreaseCorners
public import Unfoldings.Cap.RestrictedSectionSum

/-! Sharp distortion of an actual one-plane corner on a restricted bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
theorem abs_restrictedBoundaryTurnError_le_sharp_of_flat_fan (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (f : Face)
    (flat : ∀ c : (C.restrictFaces U).Corner,
      (C.restrictFaces U).vertexOfCorner Set.univ c =
        (C.restrictFaces U).boundaryEndVertex Set.univ p → K.normalSlope c.1.val = K.normalSlope f)
    (short : (C.restrictFaces U).regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
      ((C.restrictFaces U).boundaryEndVertex Set.univ p) ≤ π) :
    |K.restrictedBoundaryTurnError U p| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  obtain ⟨n, chain, _first, _last, covers⟩ := R.exists_boundary_link Set.univ p
  let c := C.includeRestrictedLinkChain U chain
  have slope (i : Fin (n + 1)) : K.normalSlope (c.point i).val.1.1 = K.normalSlope f :=
    flat (chain.point i).val.1 (chain.point i).property
  have projected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w chain covers (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  have intrinsic : (∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.totalAngle Set.univ w := R.sum_linkCornerAngle Set.univ w chain covers
  have h := K.abs_flat_link_projection_error_le_sharp c nonnegative small tilt f slope
    (K.projectedInterval_halfplane_of_sum_le_pi c (projected.trans_le short))
  rw [intrinsic, projected] at h
  change |(π - R.totalAngle Set.univ w) - (π -
    R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)| ≤ _
  rwa [sub_sub_sub_cancel_left, abs_sub_comm]

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
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    |K.restrictedBoundaryTurnError U p| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
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
  have estimate := K.abs_link_projection_error_of_crease_ray c internal slopes
    (by rwa [first_ray, last_ray]) (by rwa [first_ray, last_ray]) height nonnegative small tilt
  have projected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w chain covers (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  have intrinsic : (∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.totalAngle Set.univ w :=
    R.sum_linkCornerAngle Set.univ w chain covers
  rw [intrinsic, projected] at estimate
  change |(π - R.totalAngle Set.univ w) - (π -
    R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)| ≤ _
  rwa [sub_sub_sub_cancel_left, abs_sub_comm]

end Unfoldings.ConvexCap
