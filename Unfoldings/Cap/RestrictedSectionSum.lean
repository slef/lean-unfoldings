module

public import Unfoldings.Cap.ActiveSectionVariation
public import Unfoldings.Cap.RestrictedSectionDirections

/-! Straight restricted-boundary fan errors summed without choosing a boundary traversal order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Actual intrinsic exterior fan turn minus its actual projected exterior fan turn. -/
def restrictedBoundaryTurnError (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) : ℝ :=
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  (Real.pi - R.totalAngle Set.univ w) -
    (Real.pi - R.regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)

open Classical in
/-- Only physical collinear contacts and opposite projected bank rays are inputs to this sum. -/
theorem sum_abs_restricted_section_error_le_tilt {I : Type*} [Fintype I] (U : Set Face)
    (bank : I → (C.restrictFaces U).BoundaryEnd Set.univ) (origin direction : Plane)
    (unit : ‖direction‖ = 1) (time : I → ℝ) (distinct : Function.Injective time)
    (position : ∀ i, Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (bank i)) =
      origin + time i • direction)
    (inside : ∀ i, origin + time i • direction ∈ interior K.footprint)
    (a b : I → ℝ) (opposite : ∀ i, a i * b i < 0)
    (outgoing : ∀ i, Cap.horizontal ((K.folding.restrictFaces U).germDirection (bank i).val) =
      a i • direction)
    (incoming : ∀ i, Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ (bank i)).val) = b i • direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i, |K.restrictedBoundaryTurnError U (bank i)|) ≤ 2 * φ := by
  let R := C.restrictFaces U
  let face (i : I) (side : Bool) : Face :=
    if side then (R.boundaryMate Set.univ (bank i)).val.1.1.val else (bank i).val.1.1.val
  have active (i : I) (side : Bool) :
      K.supportHeight (face i side) (origin + time i • direction) =
        K.roofHeight (origin + time i • direction) := by
    cases side
    · have present := K.restricted_bank_face_active U (bank i)
      rw [position] at present
      exact present
    · have present := K.restricted_bank_face_active U (R.boundaryMate Set.univ (bank i))
      rw [(K.folding.restrictFaces U).boundaryPosition_mate, position] at present
      exact present
  have nonzero : direction ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  have pointwise (i : I) : |K.restrictedBoundaryTurnError U (bank i)| ≤
      InnerProductGeometry.angle (K.spatialDirection (face i false) direction)
        (K.spatialDirection (face i true) direction) := by
    have internal : ¬ C.IsBoundaryVertex Set.univ
        (C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ (bank i))) := by
      apply (K.projectedVertex_mem_interior_iff _).mp
      rw [K.projected_restricted_boundaryPosition U, position]
      exact inside i
    exact K.restricted_fan_error_le_active_angle U (bank i) direction nonzero internal
      (a i) (b i) (opposite i) (outgoing i) (incoming i)
  exact (Finset.sum_le_sum (fun i _ => pointwise i)).trans
    (K.sum_active_section_angles_le_tilt origin direction unit time distinct face active
      nonnegative small tilt)

end Unfoldings.ConvexCap
