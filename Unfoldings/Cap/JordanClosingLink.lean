module

public import Unfoldings.Cap.JordanLocalSection

/-! Derive actual closing-link fan errors directly from the closed geometric curve decomposition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Excluding the closed remainder gives a straight component with error at most 2φ. -/
theorem sum_abs_jordan_closing_link_error_le_tilt (inside : J ⊆ interior K.footprint)
    (selected : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1)))
    (a b : Plane) (different : a ≠ b) (remainder : Set Plane) (closed : IsClosed remainder)
    (cover : J ⊆ segment ℝ a b ∪ remainder)
    (outside : ∀ i ∈ selected,
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
        ((K.jordanContour jordan contains avoids).cycle.point i)) ∉ remainder)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i|) ≤ 2 * φ := by
  let direction := NormedSpace.normalize (b - a)
  have nonzero : b - a ≠ 0 := sub_ne_zero.mpr different.symm
  have unit : ‖direction‖ = 1 := NormedSpace.norm_normalize nonzero
  apply K.sum_abs_jordan_locally_straight_error_le_tilt jordan contains avoids inside selected
    a direction unit _ nonnegative small tilt
  intro i member
  filter_upwards [closed.isOpen_compl.mem_nhds (outside i member)] with x absent
  intro on_curve
  have on_segment : x ∈ segment ℝ a b := (cover on_curve).resolve_right absent
  obtain ⟨t, _bounds, at_x⟩ := (segment_eq_image_lineMap ℝ a b).le on_segment
  refine ⟨t * ‖b - a‖, ?_⟩
  rw [← at_x, AffineMap.lineMap_apply_module']
  change t • (b - a) + a = a + (t * ‖b - a‖) • NormedSpace.normalize (b - a)
  rw [mul_smul, NormedSpace.norm_smul_normalize, add_comm]

end Unfoldings.ConvexCap
