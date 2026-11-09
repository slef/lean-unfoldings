module

public import Unfoldings.Geometry.PyramidAngles
public import Unfoldings.Geometry.FiniteAngles

/-! Every nonempty finite transverse pyramid has a strict lateral angle budget. -/

@[expose] public section

namespace Unfoldings

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Nonempty ι]

theorem pyramid_angle_budget_strict_of_nonzero_level (next : Equiv.Perm ι)
    (apex : E) (base : ι → E) (f : E →L[ℝ] ℝ) (h : ℝ) (nonzero : h ≠ 0)
    (level : ∀ i, f (base i - apex) = h) :
    (∑ i, EuclideanGeometry.angle (base i) apex (base (next i))) +
      (∑ i, EuclideanGeometry.angle (base (next.symm i)) (base i) (base (next i))) <
      (Fintype.card ι : ℝ) * Real.pi :=
  pyramid_angle_budget_strict_of_level next apex base f h nonzero level
    (exists_corner_angle_ne_pi base next.symm next apex)

end Unfoldings
