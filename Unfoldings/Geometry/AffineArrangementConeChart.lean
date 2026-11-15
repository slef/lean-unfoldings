module

public import Unfoldings.Geometry.AffineArrangementLocalCone
public import Mathlib.Topology.MetricSpace.Isometry

/-! Actual isometric cell-ball coordinates on finite affine cells at their active tangent cones. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite I] (f : I → E →ᵃ[ℝ] ℝ) (signs : I → Bool)

omit [FiniteDimensional ℝ E] [Finite I] in
/-- Translation identifies an actual whole cell ball with its active tangent-cone ball. -/
def tangentCellBallEquiv (x : closedChamber f signs) (r : ℝ)
    (local_eq : ∀ z, dist z x.val < r →
      (z ∈ closedChamber f signs ↔ z - x.val ∈ tangentCell f signs x.val)) :
    Metric.ball x r ≃ᵢ
      Metric.ball (⟨0, zero_mem_tangentCell f signs x.val⟩ : tangentCell f signs x.val) r where
  toFun z := ⟨⟨z.val.val - x.val,
    (local_eq z.val.val (Metric.mem_ball.mp z.property)).mp z.val.property⟩, by
      change dist (z.val.val - x.val) 0 < r
      simpa only [Subtype.dist_eq, dist_eq_norm, sub_zero] using (Metric.mem_ball.mp z.property)⟩
  invFun v := ⟨⟨v.val.val + x.val, by
    apply (local_eq (v.val.val + x.val) ?_).mpr
    · simpa only [add_sub_cancel_right] using v.val.property
    · simpa only [Subtype.dist_eq, dist_eq_norm, add_sub_cancel_right, sub_zero] using
        (Metric.mem_ball.mp v.property)⟩, by
      change dist (v.val.val + x.val) x.val < r
      simpa only [Subtype.dist_eq, dist_eq_norm, add_sub_cancel_right, sub_zero] using
        (Metric.mem_ball.mp v.property)⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact sub_add_cancel _ _
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_sub_cancel_right _ _
  isometry_toFun := by
    intro z w
    change edist (z.val.val - x.val) (w.val.val - x.val) = edist z.val.val w.val.val
    exact edist_sub_right _ _ _

omit [FiniteDimensional ℝ E] [Finite I] in
@[simp] theorem tangentCellBallEquiv_apply (x : closedChamber f signs) (r : ℝ)
    (local_eq : ∀ z, dist z x.val < r →
      (z ∈ closedChamber f signs ↔ z - x.val ∈ tangentCell f signs x.val))
    (z : Metric.ball x r) :
    (tangentCellBallEquiv f signs x r local_eq z).val.val = z.val.val - x.val := rfl

/-- Every actual finite affine cell has a whole-ball cone isometry, including at corners. -/
theorem exists_tangentCell_ball_isometry (x : closedChamber f signs) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : Metric.ball x r ≃ᵢ
      Metric.ball (⟨0, zero_mem_tangentCell f signs x.val⟩ : tangentCell f signs x.val) r,
        ∀ z, (A z).val.val = z.val.val - x.val := by
  obtain ⟨r, positive, local_eq⟩ :=
    exists_radius_mem_closedChamber_iff_tangent f signs x.property
  exact ⟨r, positive, tangentCellBallEquiv f signs x r local_eq, fun _ => rfl⟩

end Unfoldings.AffineArrangement
