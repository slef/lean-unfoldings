module

public import Unfoldings.Geometry.PolygonalChain
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-! A common direction wedge of width at most pi/2 gives whole-edge radial monotonicity. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed positive span of two directed boundary rays. -/
def InDirectionWedge (u v x : E) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v

/-- Every pair of directions in a nonobtuse wedge has nonnegative scalar product. -/
theorem inner_nonneg_of_inDirectionWedge {u v x y : E}
    (opening : 0 ≤ inner ℝ u v) (first : InDirectionWedge u v x)
    (last : InDirectionWedge u v y) : 0 ≤ inner ℝ x y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := first
  obtain ⟨c, d, hc, hd, rfl⟩ := last
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have reverse : 0 ≤ inner ℝ v u := by simpa only [real_inner_comm] using opening
  have uu : 0 ≤ inner ℝ u u := real_inner_self_nonneg
  have vv : 0 ≤ inner ℝ v v := real_inner_self_nonneg
  positivity

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain E n)

/-- A real width bound on a single positive-span direction wedge for all actual edges. -/
def AngleMonotone (width : ℝ) : Prop :=
  ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v ≤ width ∧
    ∀ i, InDirectionWedge u v (P.edge i)

theorem AngleMonotone.pairwiseNonnegativeEdges {width : ℝ} (monotone : P.AngleMonotone width)
    (nonobtuse : width ≤ Real.pi / 2) : P.PairwiseNonnegativeEdges := by
  obtain ⟨u, v, _une, _vne, angle, directions⟩ := monotone
  have opening : 0 ≤ inner ℝ u v := by
    by_contra negative
    have too_large := InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.mp
      (lt_of_not_ge negative)
    exact (not_lt_of_ge (angle.trans nonobtuse)) too_large
  intro i j
  exact inner_nonneg_of_inDirectionWedge opening (directions i) (directions j)

/-- O'Rourke's angle-monotone-to-radially-monotone implication, on entire edges. -/
theorem AngleMonotone.radiallyMonotone {width : ℝ} (monotone : P.AngleMonotone width)
    (nonobtuse : width ≤ Real.pi / 2) : P.RadiallyMonotone :=
  PairwiseNonnegativeEdges.radiallyMonotone P
    (AngleMonotone.pairwiseNonnegativeEdges P monotone nonobtuse)

end PolygonalChain
end Unfoldings
