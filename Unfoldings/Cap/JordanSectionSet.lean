module

public import Unfoldings.Cap.RestrictedSectionSum
public import Unfoldings.Cap.JordanBankTurnBounds

/-! Straight closing-link error bounds for arbitrary actual contour vertex sets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Bound a closing link without supplying a sorted traversal or cyclic interval. -/
theorem sum_abs_jordan_section_set_error_le_tilt (inside : J ⊆ interior K.footprint)
    (selected : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1)))
    (origin direction : Plane) (unit : ‖direction‖ = 1)
    (collinear : ∀ i ∈ selected, ∃ t : ℝ,
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
        ((K.jordanContour jordan contains avoids).cycle.point i)) = origin + t • direction)
    (rays : ∀ i ∈ selected, ∃ a b : ℝ, a * b < 0 ∧
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).germDirection
        ((K.jordanContour jordan contains avoids).cycle.point i).val) = a • direction ∧
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).germDirection
        ((C.restrictFaces (K.jordanFaces J)).boundaryMate Set.univ
          ((K.jordanContour jordan contains avoids).cycle.point i)).val) = b • direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i|) ≤ 2 * φ := by
  classical
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let Q := K.jordanContour jordan contains avoids
  let bank (i : selected) := Q.cycle.point i.val
  choose time position using (fun i : selected => collinear i.val i.property)
  choose a b opposite outgoing incoming using (fun i : selected => rays i.val i.property)
  have distinct : Function.Injective time := by
    intro i j equal
    apply Subtype.ext
    apply (K.jordanContourVertexEquiv jordan contains avoids).injective
    apply Subtype.ext
    apply K.projectedVertex_injective
    change K.projectedVertex (C.includeRestrictedVertexUniv U
        (R.boundaryEndVertex Set.univ (bank i))) =
      K.projectedVertex (C.includeRestrictedVertexUniv U
        (R.boundaryEndVertex Set.univ (bank j)))
    rw [K.projected_restricted_boundaryPosition U, K.projected_restricted_boundaryPosition U,
      position i, position j, equal]
  have section_inside (i : selected) : origin + time i • direction ∈ interior K.footprint := by
    have on_curve : K.projectedVertex (C.includeRestrictedVertexUniv U
        (R.boundaryEndVertex Set.univ (bank i))) ∈ J :=
      (K.jordan_isBoundaryVertex_iff jordan contains avoids _).mp
        (R.boundaryEndAsVertex Set.univ (bank i)).property
    rw [K.projected_restricted_boundaryPosition U, position] at on_curve
    exact inside on_curve
  have bound := K.sum_abs_restricted_section_error_le_tilt U bank origin direction unit time
    distinct position section_inside a b opposite outgoing incoming nonnegative small tilt
  have sum_eq : (∑ i : selected, |K.restrictedBoundaryTurnError U (bank i)|) =
      ∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i| := by
    exact (Finset.sum_subtype selected (by simp)
      (fun i => |K.jordanContourTurnError jordan contains avoids i|)).symm
  rw [sum_eq] at bound
  exact bound

end Unfoldings.ConvexCap
