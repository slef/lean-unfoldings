module

public import Unfoldings.Cone.IntervalCompatibility

/-!
# Actual interval-link fans are isometric to their angular models

The cellwise inverse respects every actual seam, so it descends to a
nonexpanding inverse of the angular-to-tangent map. Both round trips are
verified on the original cells. This gives an actual metric isometry for
every boundary vertex, without a spatial-folding assumption.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def tangentToIntervalAngular {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) :
    C.TangentFan retain v → (C.linkAngularFan retain v chain).Surface :=
  MetricGluing.lift (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentCellToAngular retain v chain covers)
    (C.tangentCellToAngular_lipschitz retain v chain covers)
    (C.tangentCellToAngular_interval_compatible retain v chain covers start finish)

@[simp] theorem tangentToIntervalAngular_faceMap {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) (q : C.CornerAt retain v) (x : C.TangentCell retain v q) :
    C.tangentToIntervalAngular retain v chain covers start finish
      (C.tangentFaceMap retain v q x) = C.tangentCellToAngular retain v chain covers q x := rfl

theorem tangentToIntervalAngular_lipschitz {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) :
    LipschitzWith 1 (C.tangentToIntervalAngular retain v chain covers start finish) :=
  MetricGluing.lift_lipschitz (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentCellToAngular retain v chain covers)
    (C.tangentCellToAngular_lipschitz retain v chain covers)
    (C.tangentCellToAngular_interval_compatible retain v chain covers start finish)

theorem tangentCellToAngular_linkSector_symm {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (i : Fin (n + 1)) (x : (C.linkAngularFan retain v chain).Cell i) :
    C.tangentCellToAngular retain v chain covers (C.linkCornerAt retain v chain i)
      ((C.linkSectorIsometry retain v chain i).symm x) =
      (C.linkAngularFan retain v chain).faceMap i x := by
  apply C.tangentCellToAngular_of_coordinates retain v chain covers _ _ i x rfl
  have coordinates := C.linkSectorIsometry_agrees retain v chain i
    ((C.linkSectorIsometry retain v chain i).symm x)
  rw [IsometryEquiv.apply_symm_apply] at coordinates
  exact coordinates.symm

theorem angularToTangent_tangentToIntervalAngular {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) (z : C.TangentFan retain v) :
    C.angularToTangent retain v chain
      (C.tangentToIntervalAngular retain v chain covers start finish z) = z := by
  obtain ⟨⟨q, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) z
  change C.angularToTangent retain v chain
    (C.tangentToIntervalAngular retain v chain covers start finish
      (C.tangentFaceMap retain v q x)) = _
  rw [C.tangentToIntervalAngular_faceMap]
  exact C.angularToTangent_tangentCellToAngular retain v chain covers q x

theorem tangentToIntervalAngular_angularToTangent {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) (z : (C.linkAngularFan retain v chain).Surface) :
    C.tangentToIntervalAngular retain v chain covers start finish
      (C.angularToTangent retain v chain z) = z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.linkAngularFan retain v chain).Cell (C.linkAngularFan retain v chain).glue z
  change C.tangentToIntervalAngular retain v chain covers start finish
    (C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap i x)) = _
  rw [C.angularToTangent_faceMap]
  change C.tangentToIntervalAngular retain v chain covers start finish
    (C.tangentFaceMap retain v (C.linkCornerAt retain v chain i)
      ((C.linkSectorIsometry retain v chain i).symm x)) = _
  rw [C.tangentToIntervalAngular_faceMap]
  exact C.tangentCellToAngular_linkSector_symm retain v chain covers i x

theorem angularToTangent_isometry_of_interval {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) : Isometry (C.angularToTangent retain v chain) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (C.angularToTangent_lipschitz retain v chain).edist_le_mul x y
  · have bound :=
      (C.tangentToIntervalAngular_lipschitz retain v chain covers start finish).edist_le_mul
        (C.angularToTangent retain v chain x) (C.angularToTangent retain v chain y)
    simpa only [ENNReal.coe_one, one_mul,
      C.tangentToIntervalAngular_angularToTangent retain v chain covers start finish] using bound

/-- A boundary link's intrinsic tangent metric is exactly the assembled angular fan metric. -/
def intervalFanIsometry {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) :
    (C.linkAngularFan retain v chain).Surface ≃ᵢ C.TangentFan retain v where
  toFun := C.angularToTangent retain v chain
  invFun := C.tangentToIntervalAngular retain v chain covers start finish
  left_inv := C.tangentToIntervalAngular_angularToTangent retain v chain covers start finish
  right_inv := C.angularToTangent_tangentToIntervalAngular retain v chain covers start finish
  isometry_toFun := C.angularToTangent_isometry_of_interval retain v chain covers start finish

@[simp] theorem intervalFanIsometry_apply {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) (z : (C.linkAngularFan retain v chain).Surface) :
    C.intervalFanIsometry retain v chain covers start finish z =
      C.angularToTangent retain v chain z :=
  rfl

/-- Every actual boundary vertex has an angular fan model with the correct total angle. -/
theorem exists_boundaryFanIsometry (boundary : C.IsBoundaryVertex retain v) :
    ∃ n, ∃ A : AngularFan n, A.totalAngle = C.totalAngle retain v ∧
      Nonempty (A.Surface ≃ᵢ C.TangentFan retain v) := by
  obtain ⟨n, chain, start, finish, covers⟩ := C.exists_interval_link retain v boundary
  exact ⟨n, C.linkAngularFan retain v chain,
    C.linkAngularFan_totalAngle retain v chain covers,
    ⟨C.intervalFanIsometry retain v chain covers start finish⟩⟩

end Unfoldings.TriangleComplex
