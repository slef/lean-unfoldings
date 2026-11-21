module

public import Unfoldings.Cap.SharpRestrictedStraightTurns

/-! Sum the angle errors along an actual regular straight cap section. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The plane labels of a flat contact or of a genuine transverse crease. -/
def HasRegularSectionSlopes (w : C.Vertex Set.univ) (direction : Plane) : Prop :=
  ∃ a b : Plane,
    (∀ f i, C.vertexOfCorner Set.univ (f, i) = w → K.normalSlope f = a ∨ K.normalSlope f = b) ∧
    (a = b ∨ inner ℝ (a - b) direction ≠ 0)

open Classical in
/-- The sharp local hinge costs sum along the actual line, with repeated
subdivision vertices contributing no bend. -/
theorem sum_abs_restricted_section_error_le_sin_tilt {I : Type*} [Fintype I] (U : Set Face)
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
    (regular : ∀ i, K.HasRegularSectionSlopes (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ (bank i))) direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i, |K.restrictedBoundaryTurnError U (bank i)|) ≤ 2 * φ * sin φ := by
  let R := C.restrictFaces U
  let bend (i : I) := angle (K.spatialDirection (bank i).val.1.1.val direction)
    (K.spatialDirection (R.boundaryMate Set.univ (bank i)).val.1.1.val direction)
  have pointwise (i : I) : |K.restrictedBoundaryTurnError U (bank i)| ≤ sin φ * bend i := by
    have internal : ¬ C.IsBoundaryVertex Set.univ
        (C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ (bank i))) := by
      apply (K.projectedVertex_mem_interior_iff _).mp
      rw [K.projected_restricted_boundaryPosition U, position]
      exact inside i
    obtain ⟨u, v, slopes, transverse⟩ := regular i
    rcases mul_neg_iff.mp (opposite i) with ⟨a_pos, b_neg⟩ | ⟨a_neg, b_pos⟩
    · exact K.abs_restrictedBoundaryTurnError_le_sin_mul_active_angle nonnegative small tilt U
        (bank i) direction u v internal slopes transverse a_pos (neg_pos.mpr b_neg)
        (outgoing i) (by rw [neg_smul, smul_neg, neg_neg]; exact incoming i)
    · have reversed : u = v ∨ inner ℝ (u - v) (-direction) ≠ 0 := by
        rw [inner_neg_right, neg_ne_zero]
        exact transverse
      have h := K.abs_restrictedBoundaryTurnError_le_sin_mul_active_angle nonnegative small tilt U
        (bank i) (-direction) u v internal slopes reversed (neg_pos.mpr a_neg) b_pos
        (by rw [neg_smul, smul_neg, neg_neg]; exact outgoing i)
        (by rw [neg_neg]; exact incoming i)
      have turn (f : Face) : K.spatialDirection f (-direction) = -K.spatialDirection f direction := by
        simp only [spatialDirection, pullbackDirection, map_neg]
      rw [turn, turn, angle_neg_neg] at h
      exact h
  have sum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => pointwise i)
  rw [← Finset.mul_sum] at sum
  have spatial := K.sum_restricted_section_active_angles_le_tilt U bank origin direction unit time
    distinct position nonnegative small tilt
  have sine : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos])
  exact sum.trans ((mul_le_mul_of_nonneg_left spatial sine).trans_eq (mul_comm _ _))

end Unfoldings.ConvexCap
