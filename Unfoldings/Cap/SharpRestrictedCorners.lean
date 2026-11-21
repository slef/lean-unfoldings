module

public import Unfoldings.Cap.SharpSectionFans
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

end Unfoldings.ConvexCap
