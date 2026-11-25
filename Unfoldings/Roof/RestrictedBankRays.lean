module

public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Geometry.LocalLineSegment
public import Unfoldings.Roof.SharpLinkFans
public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Complex.BoundaryEndDistinct
public import Unfoldings.Complex.FaceRestrictionLinks

/-! Actual projected boundary banks cannot leave one vertex in the same positive direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- The entire projected directed bank is the actual affine edge segment. -/
theorem restrictProjection_directedBoundaryPath (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (t : unitInterval) :
    K.restrictProjection U ((C.restrictFaces U).directedBoundaryPath p t) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) +
        t.val • Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) := by
  change Cap.horizontal ((K.folding.restrictFaces U).toSpace Set.univ _) = _
  rw [(K.folding.restrictFaces U).directedBoundaryPath_position, map_add, map_smul]

open Classical in
/-- The two actual banks at one restricted vertex have different projected positive rays. -/
theorem restricted_boundary_rays_angle_ne_zero (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) ≠ 0 := by
  classical
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  intro zero
  obtain ⟨_genuine, r, rp, scaled⟩ := InnerProductGeometry.angle_eq_zero_iff.mp zero
  let den := 2 * (1 + r)
  have denpos : 0 < den := by dsimp [den]; positivity
  let t : unitInterval := ⟨r / den, (div_pos rp denpos).le,
    ((div_lt_one denpos).mpr (by dsimp [den]; linarith)).le⟩
  let s : unitInterval := ⟨1 / den, (div_pos zero_lt_one denpos).le,
    ((div_lt_one denpos).mpr (by dsimp [den]; linarith)).le⟩
  have tp : 0 < t.val := div_pos rp denpos
  have ts : t.val < 1 := (div_lt_one denpos).mpr (by dsimp [den]; linarith)
  have projected : K.restrictProjection U (R.directedBoundaryPath p t) =
      K.restrictProjection U (R.directedBoundaryPath q s) := by
    rw [K.restrictProjection_directedBoundaryPath, K.restrictProjection_directedBoundaryPath,
      F.boundaryPosition_mate, scaled, smul_smul]
    have coefficient : t.val = s.val * r := by
      change r / den = 1 / den * r
      ring
    rw [coefficient]
  let bank := (R.boundaryEndEquiv Set.univ p).1
  let other := (R.boundaryEndEquiv Set.univ q).1
  let x := R.bankParameterFromEnd bank (R.boundaryEndEquiv Set.univ p).2 t
  let y := R.bankParameterFromEnd other (R.boundaryEndEquiv Set.univ q).2 s
  have regular : ¬ (C.triangle bank.val.face.val).IsVertex x.val :=
    R.bankParameterFromEnd_nonvertex bank _ t tp ts
  have same := K.restrictProjection_fiber_regular U bank.val.face
    ((R.triangle bank.val.face).edgeMap bank.val.edge x) regular (R.directedBoundaryPath q s)
    projected
  have different : bank ≠ other := by
    intro equal
    have ends := F.boundaryEnd_eq_of_same_bank_vertex Set.univ p q equal
      (R.boundaryMate_spec Set.univ p).2.symm
    exact (R.boundaryMate_spec Set.univ p).1 ends.symm
  exact R.bankMap_ne_of_ne Set.univ different x y regular same

open Classical in
/-- The projected germ of any actual boundary bank follows the local frontier line. -/
theorem restricted_bank_direction_of_local_line (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (direction : Plane)
    (locally : ∀ᶠ x in 𝓝 (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p)),
      x ∈ frontier (K.restrictedCarrier U) → ∃ a : ℝ,
      x = Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) + a • direction) :
    ∃ a : ℝ, Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • direction := by
  apply exists_smul_of_locally_in_line _ _ direction _ _ locally
  intro t member
  let s : unitInterval := ⟨t, member⟩
  have boundary : K.restrictProjection U ((C.restrictFaces U).directedBoundaryPath p s) ∈
      frontier (K.restrictedCarrier U) :=
    K.restricted_boundary_subset_frontier U
      ⟨(C.restrictFaces U).directedBoundaryPath p s,
        (C.restrictFaces U).directedBoundaryPath_mem_boundary p s, rfl⟩
  rw [K.restrictProjection_directedBoundaryPath] at boundary
  exact boundary

open Classical in
/-- At a straight frontier contact the two original banks have opposite rays. -/
theorem restricted_bank_rays_of_local_line (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (direction : Plane) (nonzero : direction ≠ 0)
    (locally : ∀ᶠ x in 𝓝 (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p)),
      x ∈ frontier (K.restrictedCarrier U) → ∃ a : ℝ,
      x = Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) + a • direction) :
    ∃ a b : ℝ, a * b < 0 ∧
      Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • direction ∧
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val) = b • direction := by
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  have locally_q : ∀ᶠ x in 𝓝 (Cap.horizontal (F.boundaryPosition q)),
      x ∈ frontier (K.restrictedCarrier U) →
      ∃ a : ℝ, x = Cap.horizontal (F.boundaryPosition q) + a • direction := by
    rw [show F.boundaryPosition q = F.boundaryPosition p from F.boundaryPosition_mate p]
    exact locally
  obtain ⟨a, outgoing⟩ := K.restricted_bank_direction_of_local_line U p direction locally
  obtain ⟨b, incoming⟩ := K.restricted_bank_direction_of_local_line U q direction locally_q
  have genuine (bank : R.BoundaryEnd Set.univ) : Cap.horizontal (F.germDirection bank.val) ≠ 0 := by
    let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ bank) := ⟨bank.val, rfl⟩
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    exact ray
  have an : a ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at outgoing
    exact genuine p outgoing
  have bn : b ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at incoming
    exact genuine q incoming
  have separated := K.restricted_boundary_rays_angle_ne_zero U p
  change InnerProductGeometry.angle (Cap.horizontal (F.germDirection p.val))
    (Cap.horizontal (F.germDirection q.val)) ≠ 0 at separated
  rw [outgoing, incoming] at separated
  refine ⟨a, b, ?_, outgoing, incoming⟩
  by_contra not_negative
  have positive : 0 < a * b := lt_of_le_of_ne (le_of_not_gt not_negative)
    (mul_ne_zero an bn).symm
  rcases mul_pos_iff.mp positive with ⟨ap, bp⟩ | ⟨an, bn⟩
  · rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ap,
      InnerProductGeometry.angle_smul_right_of_pos _ _ bp,
      InnerProductGeometry.angle_self nonzero] at separated
    exact separated rfl
  · rw [InnerProductGeometry.angle_smul_left_of_neg _ _ an,
      InnerProductGeometry.angle_smul_right_of_neg _ _ bn,
      InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_self nonzero] at separated
    exact separated rfl

end Unfoldings.ConvexRoof
