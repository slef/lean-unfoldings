module

public import Unfoldings.Geometry.Barycentric
public import Unfoldings.Geometry.Halfplane

/-! Edge membership and affine supporting-side tests in barycentric coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Signed area with two fixed endpoints is an affine function of the third point. -/
def orientMap (a b : Plane) : Plane →ᵃ[ℝ] ℝ :=
  (lineHeight a b).toLinearMap.toAffineMap - AffineMap.const ℝ Plane (lineHeight a b a)

@[simp] theorem orientMap_apply (a b x : Plane) : orientMap a b x = orient a b x :=
  (orient_eq_height a b x).symm

/-- An affine height changing sign along a segment has a zero on that segment. -/
theorem exists_mem_segment_zero (height : Plane →ᵃ[ℝ] ℝ) (p q : Plane)
    (positive : 0 ≤ height p) (negative : height q ≤ 0) :
    ∃ z ∈ segment ℝ p q, height z = 0 := by
  have zero' : (0 : ℝ) ∈ segment ℝ (height q) (height p) := Icc_subset_segment ⟨negative, positive⟩
  have zero : (0 : ℝ) ∈ segment ℝ (height p) (height q) := (segment_symm ℝ _ _).le zero'
  rw [← image_segment ℝ height p q] at zero
  exact zero

namespace Triangle

theorem coord_sum_edge (T : Triangle) (e : Fin 3) (x : Plane) :
    T.coord e x + T.coord (next e) x + T.coord (next (next e)) x = 1 := by
  have sum := T.sum_coord x
  rw [Fin.sum_univ_three] at sum
  fin_cases e
  · change T.coord 0 x + T.coord 1 x + T.coord 2 x = 1
    exact sum
  · change T.coord 1 x + T.coord 2 x + T.coord 0 x = 1
    linarith
  · change T.coord 2 x + T.coord 0 x + T.coord 1 x = 1
    linarith

theorem reconstruct_edge (T : Triangle) (e : Fin 3) (x : Plane) :
    x = T.coord e x • T.vertex e + T.coord (next e) x • T.vertex (next e) +
      T.coord (next (next e)) x • T.opposite e := by
  have sum := T.affineBasis.linear_combination_coord_eq_self x
  change (∑ i, T.coord i x • T.vertex i) = x at sum
  rw [Fin.sum_univ_three] at sum
  fin_cases e
  · change x = T.coord 0 x • T.vertex 0 + T.coord 1 x • T.vertex 1 + T.coord 2 x • T.vertex 2
    exact sum.symm
  · change x = T.coord 1 x • T.vertex 1 + T.coord 2 x • T.vertex 2 + T.coord 0 x • T.vertex 0
    apply sum.symm.trans
    abel
  · change x = T.coord 2 x • T.vertex 2 + T.coord 0 x • T.vertex 0 + T.coord 1 x • T.vertex 1
    apply sum.symm.trans
    abel

theorem mem_edge_iff (T : Triangle) (e : Fin 3) (x : Plane) :
    x ∈ T.edge e ↔ x ∈ T.carrier ∧ T.coord (next (next e)) x = 0 := by
  constructor
  · intro inside
    exact ⟨T.edge_subset e inside, T.coord_edge_eq_zero e ⟨x, inside⟩⟩
  · rintro ⟨inside, zero⟩
    have nonneg := T.carrier_eq_nonneg_coord.le inside
    have sum := T.coord_sum_edge e x
    rw [zero, add_zero] at sum
    have expression := T.reconstruct_edge e x
    rw [zero, zero_smul, add_zero] at expression
    exact ⟨T.coord e x, T.coord (next e) x, nonneg e, nonneg (next e), sum, expression.symm⟩

/-- Affine functions agree everywhere if they agree at the three actual corners. -/
theorem affine_ext (T : Triangle) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : Plane →ᵃ[ℝ] V) (corners : ∀ i, f (T.vertex i) = g (T.vertex i)) : f = g := by
  apply AffineMap.ext
  intro x
  have agree : Set.EqOn f g (Set.range T.vertex) := by
    rintro _ ⟨i, rfl⟩
    exact corners i
  exact AffineMap.eqOn_affineSpan agree (by rw [T.affineSpan_vertices]; trivial)

/-- An affine function vanishing along an edge is a multiple of its opposite coordinate. -/
theorem affine_height_eq_coord (T : Triangle) (e : Fin 3) (height : Plane →ᵃ[ℝ] ℝ)
    (left : height (T.vertex e) = 0) (right : height (T.vertex (next e)) = 0) (x : Plane) :
    height x = height (T.opposite e) * T.coord (next (next e)) x := by
  have first : next (next e) ≠ e := by fin_cases e <;> decide
  have second : next (next e) ≠ next e := by fin_cases e <;> decide
  have equal : height = height (T.opposite e) • T.coord (next (next e)) := by
    apply T.affine_ext
    intro i
    rcases corner_cases e i with rfl | rfl | rfl
    · simp [first, left]
    · simp [second, right]
    · simp [opposite]
  exact congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) equal

theorem orient_eq_coord_mul (T : Triangle) (e : Fin 3) (x : Plane) :
    orient (T.vertex e) (T.vertex (next e)) x =
      orient (T.vertex e) (T.vertex (next e)) (T.opposite e) * T.coord (next (next e)) x := by
  simpa only [orientMap_apply] using T.affine_height_eq_coord e
    (orientMap (T.vertex e) (T.vertex (next e)))
    (by simp only [orientMap_apply, orient_self_left])
    (by simp only [orientMap_apply, orient_self_right]) x

end Triangle
end Unfoldings
