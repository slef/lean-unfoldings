module

public import Unfoldings.Convex.FiniteDual
public import Unfoldings.Geometry.AffineArrangement

/-! Full-dimensional extension normal cells occur only at original primal vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteDual

variable {I : Type*} [Fintype I] [Nonempty I]
  (point : I → Plane) (level : I → ℝ)

/-- A clipped graph point with an open two-dimensional set of active slopes is an actual
original lifted primal vertex. No generic position or nonflat-vertex assumption is used. -/
theorem active_cell_interior_original_vertex {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) (x : Plane)
    (full : (interior {p | (clipped point level slopes compact nonempty).Active x p}).Nonempty) :
    ∃ i, point i = x ∧ (clipped point level slopes compact nonempty).height x = level i := by
  classical
  let E := clipped point level slopes compact nonempty
  let equation (i : I) : Plane →ᵃ[ℝ] ℝ :=
    (innerSL ℝ (point i - x)).toLinearMap.toAffineMap +
      AffineMap.const ℝ Plane (E.height x - level i)
  by_contra outside
  have proper (i : I) : equation i ≠ 0 := by
    intro zero
    have at0 := congrArg (fun L : Plane →ᵃ[ℝ] ℝ => L 0) zero
    change inner ℝ (point i - x) (0 : Plane) + (E.height x - level i) = 0 at at0
    rw [inner_zero_right, zero_add] at at0
    have atd := congrArg (fun L : Plane →ᵃ[ℝ] ℝ => L (point i - x)) zero
    change inner ℝ (point i - x) (point i - x) + (E.height x - level i) = 0 at atd
    have normzero : inner ℝ (point i - x) (point i - x) = 0 := by linarith
    have same : point i = x := sub_eq_zero.mp (inner_self_eq_zero.mp normzero)
    exact outside ⟨i, same, sub_eq_zero.mp at0⟩
  obtain ⟨p, inside, regular⟩ :=
    (AffineArrangement.dense_regular equation proper).inter_open_nonempty _ isOpen_interior full
  have active : E.Active x p :=
    (interior_subset (s := {r | E.Active x r})) inside
  obtain ⟨i, cost_eq⟩ := exists_cost_eq point level p
  have equality := active.2
  change E.height x = inner ℝ x p - cost point level p at equality
  rw [cost_eq] at equality
  apply regular i
  change inner ℝ (point i - x) p + (E.height x - level i) = 0
  rw [inner_sub_left]
  linarith

end Unfoldings.FiniteDual
