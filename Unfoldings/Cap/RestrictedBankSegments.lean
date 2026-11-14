module

public import Unfoldings.Cap.BoundarySectionConstruction
public import Unfoldings.Roof.CapBridge
public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Complex.BoundaryEndDistinct

/-! Actual projected boundary banks cannot leave one vertex in the same positive direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- The entire projected directed bank is the actual affine edge segment. -/
theorem restrictProjection_directedBoundaryPath (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (t : unitInterval) :
    K.toRoof.restrictProjection U ((C.restrictFaces U).directedBoundaryPath p t) =
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
  have projected : K.toRoof.restrictProjection U (R.directedBoundaryPath p t) =
      K.toRoof.restrictProjection U (R.directedBoundaryPath q s) := by
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
  have same := K.toRoof.restrictProjection_fiber_regular U bank.val.face
    ((R.triangle bank.val.face).edgeMap bank.val.edge x) regular (R.directedBoundaryPath q s)
    projected
  have different : bank ≠ other := by
    intro equal
    have ends := F.boundaryEnd_eq_of_same_bank_vertex Set.univ p q equal
      (R.boundaryMate_spec Set.univ p).2.symm
    exact (R.boundaryMate_spec Set.univ p).1 ends.symm
  exact R.bankMap_ne_of_ne Set.univ different x y regular same

end Unfoldings.ConvexCap
