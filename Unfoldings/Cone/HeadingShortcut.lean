module

public import Unfoldings.Cone.HeadingLift

/-!
# Sheet-aware shortcuts for arbitrary angular developments

Pointed heading lifts have strict apex shortcuts even when the full fan
overlaps. Any nonexpanding map preserving apex distances retains these
strict inequalities; the target may have an extended metric.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem edist_origin_eq_develop (z : A.Surface) :
    edist A.origin z = edist (0 : ℂ) (A.develop z) := by
  rw [edist_dist, edist_dist, dist_zero_left, A.norm_develop]

theorem headingLift_radial (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) :
    edist A.origin (A.headingLift a b positive small first last z) = edist (0 : ℂ) z.val := by
  rw [A.edist_origin_eq_develop, A.develop_headingLift]

theorem headingLift_edist_lt_via_origin (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z w : headingSector a b) (left_nonzero : z.val ≠ 0) (right_nonzero : w.val ≠ 0) :
    edist (A.headingLift a b positive small first last z)
        (A.headingLift a b positive small first last w) <
      edist (A.headingLift a b positive small first last z) A.origin +
        edist A.origin (A.headingLift a b positive small first last w) := by
  have strict := dist_lt_via_zero_of_mem_headingSector a b positive small
    z.property w.property left_nonzero right_nonzero
  have strict_edist : edist z.val w.val < edist z.val (0 : ℂ) + edist (0 : ℂ) w.val := by
    rw [edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr strict
  rw [(A.headingLift_isometry a b positive small first last).edist_eq,
    edist_comm (A.headingLift a b positive small first last z) A.origin,
    A.headingLift_radial, A.headingLift_radial]
  change edist z.val w.val < _
  simpa only [edist_comm] using strict_edist

/-- Strict shortening survives restoring seams and other nonexpanding maps
that preserve radial distance. -/
theorem nonexpanding_headingLift_shortcut {Y : Type*} [PseudoEMetricSpace Y]
    (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f) (o : Y)
    (radial : ∀ x, edist o (f x) = edist A.origin x)
    (a b : ℝ) (positive : 0 < b - a) (small : b - a < Real.pi)
    (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z w : headingSector a b) (left_nonzero : z.val ≠ 0) (right_nonzero : w.val ≠ 0) :
    edist (f (A.headingLift a b positive small first last z))
        (f (A.headingLift a b positive small first last w)) <
      edist (f (A.headingLift a b positive small first last z)) o +
        edist o (f (A.headingLift a b positive small first last w)) := by
  have bound := nonexpanding.edist_le_mul
    (A.headingLift a b positive small first last z) (A.headingLift a b positive small first last w)
  simp only [ENNReal.coe_one, one_mul] at bound
  apply bound.trans_lt
  rw [edist_comm (f (A.headingLift a b positive small first last z)) o, radial, radial,
    edist_comm A.origin (A.headingLift a b positive small first last z)]
  exact A.headingLift_edist_lt_via_origin a b positive small first last z w
    left_nonzero right_nonzero

end Unfoldings.AngularFan
