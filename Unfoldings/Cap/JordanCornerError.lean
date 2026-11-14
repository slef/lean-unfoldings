module

public import Unfoldings.Cap.RegionalProjectionError
public import Unfoldings.Cap.JordanBankTurnBounds

/-! Uniform actual Jordan corner errors without regularity or local-valence assumptions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- A genuine selected Jordan corner has no per-triangle or per-subdivision error charge. -/
theorem abs_jordan_corner_error_le (inside : J ⊆ interior K.footprint) {ε : ℝ}
    (nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    |K.jordanContourTurnError jordan contains avoids i| ≤ ε * (2 * Real.pi) := by
  let R := C.restrictFaces (K.jordanFaces J)
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  let w := R.boundaryEndVertex Set.univ p
  let original := C.includeRestrictedVertexUniv (K.jordanFaces J) w
  have on_curve : K.projectedVertex original ∈ J :=
    (K.jordan_isBoundaryVertex_iff jordan contains avoids w).mp
      (R.boundaryEndAsVertex Set.univ p).property
  have internal : ¬ C.IsBoundaryVertex Set.univ original :=
    (K.projectedVertex_mem_interior_iff original).mp (inside on_curve)
  have excess := K.jordan_vertex_angle_excess jordan contains avoids w
  have equality : K.jordanContourTurnError jordan contains avoids i =
      -K.regionalAngleExcess (K.jordanFaces J) original := by
    change (Real.pi - R.totalAngle Set.univ w) -
      (Real.pi - R.regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w) = _
    linarith
  rw [equality, abs_neg]
  exact K.abs_regionalAngleExcess_le_two_pi_mul nonnegative error (K.jordanFaces J)
    original internal

open Classical in
/-- One positive tilt makes every actual Jordan boundary corner uniformly close to projection. -/
theorem exists_uniform_tilt_jordan_corner_error_le {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ → ∀ {J : Set Plane}
          (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
          (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
          (i : Fin ((K.jordanContour jordan (inside.trans interior_subset) avoids).length + 1)),
            |K.jordanContourTurnError jordan (inside.trans interior_subset) avoids i| ≤ ε := by
  have tolerance : 0 < ε / (2 * Real.pi) := div_pos positive (by positivity)
  obtain ⟨φ, bounds, estimate⟩ := exists_uniform_tilt_relative_corner_angle_error.{u, v} tolerance
  refine ⟨φ, bounds, ?_⟩
  intro Face' _ C' K tilt J jordan inside avoids i
  have bound := K.abs_jordan_corner_error_le jordan (inside.trans interior_subset) avoids
    inside tolerance.le (estimate K tilt) i
  simpa only [div_mul_cancel₀ _ (ne_of_gt Real.two_pi_pos)] using bound

end Unfoldings.ConvexCap
