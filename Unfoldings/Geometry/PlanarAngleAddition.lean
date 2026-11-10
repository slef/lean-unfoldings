module

public import Unfoldings.Geometry.ConeBoundaryRays
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Exact angle addition inside an oriented planar halfplane. -/

@[expose] public section

namespace Unfoldings

/-- Consecutive positive turns inside the same closed halfplane add without wraparound. -/
theorem angle_add_of_orient_nonneg {x y z : Plane} (xne : x ≠ 0) (yne : y ≠ 0)
    (xy : 0 ≤ orient 0 x y) (xz : 0 ≤ orient 0 x z) (yz : 0 < orient 0 y z) :
    InnerProductGeometry.angle x z =
      InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by
  apply (InnerProductGeometry.angle_eq_angle_add_angle_iff yne).mpr
  by_cases zero : orient 0 x z = 0
  · left
    obtain ⟨t, equal⟩ := exists_lineMap_of_orient_eq_zero xne.symm zero
    rw [AffineMap.lineMap_apply_module'] at equal
    simp only [sub_zero, add_zero] at equal
    have identity : orient 0 y z = -t * orient 0 x y := by
      rw [equal]
      simp only [orient, PiLp.zero_apply, PiLp.smul_apply, smul_eq_mul, sub_zero]
      ring
    have negative : t < 0 := by nlinarith
    exact InnerProductGeometry.angle_eq_pi_iff.mpr ⟨xne, t, negative, equal⟩
  · right
    have positive := lt_of_le_of_ne xz (Ne.symm zero)
    have balance : orient 0 x z • y = orient 0 y z • x + orient 0 x y • z :=
      orient_zero_balance x y z
    have expression : (orient 0 y z / orient 0 x z) • x +
        (orient 0 x y / orient 0 x z) • z = y := by
      have scaled := congrArg (fun v : Plane => (orient 0 x z)⁻¹ • v) balance
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ zero, one_smul,
        div_eq_inv_mul] using scaled.symm
    rw [Submodule.mem_span_pair]
    exact ⟨⟨_, div_nonneg yz.le positive.le⟩, ⟨_, div_nonneg xy positive.le⟩, expression⟩

end Unfoldings
