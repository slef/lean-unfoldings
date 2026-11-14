module

public import Unfoldings.Cap.BoundarySectionConstruction
public import Unfoldings.Cap.JordanBankTurnBounds

/-! Uniform fan error bounds on actual straight portions of the constructed Jordan contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Only the literal straight contour coordinates and their order are inputs to this comparison. -/
theorem sum_abs_jordan_straight_interval_error_le_tilt (inside : J ⊆ interior K.footprint)
    (origin direction : Plane) (unit : ‖direction‖ = 1) (first turns : ℕ)
    (fits : first + turns + 1 ≤ (K.jordanContour jordan contains avoids).length)
    (time : Fin (turns + 2) → ℝ) (increasing : StrictMono time)
    (projection : ∀ i : Fin (turns + 2),
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
        ((K.jordanContour jordan contains avoids).cycle.point ⟨first + i.val, by omega⟩)) =
        origin + time i • direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i : Fin turns, |K.jordanContourTurnError jordan contains avoids
      ⟨first + i.val + 1, by omega⟩|) ≤ 2 * φ := by
  let R := C.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  have fits_Q : first + turns + 1 ≤ Q.length := fits
  let T : K.BoundarySectionTrace (K.jordanFaces J) origin direction :=
    BoundarySectionTrace.ofContourInterval origin direction Q first turns fits time increasing
      projection
  have section_inside (i : Fin (turns + 2)) :
      origin + time i • direction ∈ interior K.footprint := by
    let p := Q.cycle.point (⟨first + i.val, by omega⟩ : Fin (Q.length + 1))
    have on_curve : K.projectedVertex (C.includeRestrictedVertexUniv (K.jordanFaces J)
        (R.boundaryEndVertex Set.univ p)) ∈ J :=
      (K.jordan_isBoundaryVertex_iff jordan contains avoids _).mp
        (R.boundaryEndAsVertex Set.univ p).property
    rw [K.projected_restricted_boundaryPosition (K.jordanFaces J), projection] at on_curve
    exact inside on_curve
  have bound := T.sum_abs_turnError_le_tilt_of_interior unit section_inside nonnegative small tilt
  exact bound

end Unfoldings.ConvexCap
