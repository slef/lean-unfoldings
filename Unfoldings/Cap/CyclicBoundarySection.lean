module

public import Unfoldings.Cap.BoundarySectionConstruction
public import Unfoldings.Cap.JordanBankTurnBounds
public import Unfoldings.Complex.BoundaryContourRotation

/-! Actual straight boundary sections crossing the arbitrary contour enumeration origin. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

namespace BoundarySectionTrace

variable {K}

open Classical in
/-- Rotate the actual contour to the first bank before taking its straight section. -/
def ofCyclicContourInterval {U : Set Face} (origin direction : Plane)
    (Q : (C.restrictFaces U).BoundaryContour Set.univ) (first : Fin (Q.length + 1))
    (turns : ℕ) (fits : turns + 1 ≤ Q.length)
    (time : Fin (turns + 2) → ℝ) (increasing : StrictMono time)
    (projection : ∀ i : Fin (turns + 2),
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        (Q.cycle.point (⟨i.val, by omega⟩ + first))) = origin + time i • direction) :
    K.BoundarySectionTrace U origin direction :=
  ofContourInterval origin direction (Q.rotate (C.restrictFaces U) first) 0 turns
    (by change 0 + turns + 1 ≤ Q.length; omega) time increasing (by
      intro i
      change Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        (Q.cycle.point (⟨0 + i.val, by omega⟩ + first))) = _
      simpa only [Nat.zero_add] using projection i)

end BoundarySectionTrace

variable {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- The same subdivision-independent bound holds when a closing section crosses index zero. -/
theorem sum_abs_jordan_cyclic_straight_interval_error_le_tilt
    (inside : J ⊆ interior K.footprint) (origin direction : Plane) (unit : ‖direction‖ = 1)
    (first : Fin ((K.jordanContour jordan contains avoids).length + 1)) (turns : ℕ)
    (fits : turns + 1 ≤ (K.jordanContour jordan contains avoids).length)
    (time : Fin (turns + 2) → ℝ) (increasing : StrictMono time)
    (projection : ∀ i : Fin (turns + 2),
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
        ((K.jordanContour jordan contains avoids).cycle.point
          (⟨i.val, by omega⟩ + first))) = origin + time i • direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i : Fin turns, |K.jordanContourTurnError jordan contains avoids
      (⟨i.val + 1, by omega⟩ + first)|) ≤ 2 * φ := by
  let R := C.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  have fits_Q : turns + 1 ≤ Q.length := fits
  let T : K.BoundarySectionTrace (K.jordanFaces J) origin direction :=
    BoundarySectionTrace.ofCyclicContourInterval origin direction Q first turns fits time
      increasing projection
  have section_inside (i : Fin (turns + 2)) :
      origin + time i • direction ∈ interior K.footprint := by
    let p := Q.cycle.point (⟨i.val, by omega⟩ + first)
    have on_curve : K.projectedVertex (C.includeRestrictedVertexUniv (K.jordanFaces J)
        (R.boundaryEndVertex Set.univ p)) ∈ J :=
      (K.jordan_isBoundaryVertex_iff jordan contains avoids _).mp
        (R.boundaryEndAsVertex Set.univ p).property
    rw [K.projected_restricted_boundaryPosition (K.jordanFaces J), projection] at on_curve
    exact inside on_curve
  have bound := T.sum_abs_turnError_le_tilt_of_interior unit section_inside nonnegative small tilt
  simp only [T, Q, BoundarySectionTrace.turnError, BoundarySectionTrace.ofCyclicContourInterval,
    BoundarySectionTrace.ofContourInterval, BoundarySectionTrace.ofProjected,
    TriangleComplex.BoundaryContour.rotate, finCycle_apply, Fin.val_succ, Fin.val_castSucc,
    Nat.zero_add, jordanContourTurnError] at bound ⊢
  convert bound using 1
  rfl

end Unfoldings.ConvexCap
