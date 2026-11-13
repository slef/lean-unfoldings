module

public import Unfoldings.Examples.Pyramid.Coordinates

/-! Explicit upward unit supporting normals of the four genuine pyramid faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

def normal (f : Bool × Bool) : Space := (Real.sqrt 3)⁻¹ • vec3 (sign f.1) (sign f.2) 1

theorem normal_unit (f : Bool × Bool) : ‖normal f‖ = 1 := by
  have positive : 0 < Real.sqrt 3 := by positivity
  have normed : ‖vec3 (sign f.1) (sign f.2) 1‖ = Real.sqrt 3 := by
    apply (sq_eq_sq₀ (norm_nonneg _) positive.le).mp
    rw [EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt (by norm_num)]
    norm_num [vec3, Fin.sum_univ_three]
  rw [normal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
    normed, inv_mul_cancel₀ positive.ne']

theorem normal_upward (f : Bool × Bool) : 0 < normal f 2 := by
  change 0 < (Real.sqrt 3)⁻¹ * 1
  positivity

theorem constant_normal_height (f : Bool × Bool) (x : Plane) :
    inner ℝ (normal f) (placement f x) = (Real.sqrt 3)⁻¹ := by
  rw [placement_coordinates]
  have sum : triangle.coord 0 x + triangle.coord 1 x + triangle.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using triangle.sum_coord x
  obtain ⟨a, b⟩ := f
  cases a <;> cases b
  all_goals
    simp only [normal, PiLp.inner_apply, Fin.sum_univ_three,
      vec3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      sign, Bool.false_eq_true, ite_false, ite_true]
    calc
      _ = (Real.sqrt 3)⁻¹ * (triangle.coord 0 x + triangle.coord 1 x + triangle.coord 2 x) := by
        simp
        ring
      _ = _ := by rw [sum, mul_one]

theorem normal_tangent (f : Bool × Bool) (x : Plane) :
    inner ℝ (normal f) ((placement f).linear x) = 0 := by
  have chord : (placement f).linear x = placement f x - placement f 0 := by
    have equality := (placement f).toAffineMap.linear_apply_vsub x 0
    change (placement f).linear (x - 0) = placement f x - placement f 0 at equality
    simpa only [sub_zero] using equality
  rw [chord, inner_sub_right, constant_normal_height, constant_normal_height, sub_self]

theorem normal_vertex_le (f g : Bool × Bool) (i : Fin 3) :
    inner ℝ (normal f) (vertex g i) ≤ (Real.sqrt 3)⁻¹ := by
  have nonnegative : 0 ≤ (Real.sqrt 3)⁻¹ := by positivity
  obtain ⟨a, b⟩ := f
  obtain ⟨c, d⟩ := g
  cases a <;> cases b <;> cases c <;> cases d <;> fin_cases i <;>
    norm_num [normal, vertex, vec3, sign, PiLp.inner_apply, Fin.sum_univ_three]

/-- Every original face lies on the inward side of each of the four supporting planes. -/
theorem supporting (f g : Bool × Bool) (x : triangle.Cell) :
    inner ℝ (normal f) (placement g x.val - placement f 0) ≤ 0 := by
  let height : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ (normal f)).toLinearMap.toAffineMap.comp
    (placement g).toAffineMap
  have convex : Convex ℝ {p | height p ≤ (Real.sqrt 3)⁻¹} :=
    (convex_Iic ((Real.sqrt 3)⁻¹)).affine_preimage height
  have bound : triangle.carrier ⊆ {p | height p ≤ (Real.sqrt 3)⁻¹} := by
    apply convexHull_min _ convex
    rintro _ ⟨i, rfl⟩
    change inner ℝ (normal f) (placement g (triangle.vertex i)) ≤ _
    rw [placement_vertex]
    exact normal_vertex_le f g i
  rw [inner_sub_right, constant_normal_height]
  exact sub_nonpos.mpr (bound x.property)

end Unfoldings.Examples.Pyramid
