module

public import Unfoldings.Cone.Sector

/-! Genuine angular distance is at most any real unreduced heading difference. -/

@[expose] public section

namespace Unfoldings

/-- Real headings may make full turns; their absolute difference still bounds angular distance. -/
theorem angle_polarRay_le_abs_sub (a b : ℝ) :
    InnerProductGeometry.angle (polarRay a) (polarRay b) ≤ |b - a| := by
  by_cases small : |b - a| ≤ Real.pi
  · rcases le_total a b with forward | backward
    · have nonnegative := sub_nonneg.mpr forward
      rw [abs_of_nonneg nonnegative] at small ⊢
      exact (angle_polarRay a b nonnegative small).le
    · have nonnegative := sub_nonneg.mpr backward
      have absolute : |b - a| = a - b := by rw [abs_sub_comm, abs_of_nonneg nonnegative]
      rw [absolute] at small ⊢
      rw [InnerProductGeometry.angle_comm]
      exact (angle_polarRay b a nonnegative small).le
  · exact (InnerProductGeometry.angle_le_pi _ _).trans (le_of_not_ge small)

end Unfoldings
