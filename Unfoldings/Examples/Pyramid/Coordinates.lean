module

public import Unfoldings.Geometry.SpatialTriangle
public import Unfoldings.Geometry.EdgeSides
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! A concrete four-face convex cap with apex `(0,0,1)` and diamond rim at height zero. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

def vec2 (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]
def vec3 (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

theorem exists_coordinates :
    ∃ (T : Triangle) (A : Plane →ᵃⁱ[ℝ] Space),
      A (T.vertex 0) = vec3 0 0 1 ∧ A (T.vertex 1) = vec3 1 0 0 ∧
        A (T.vertex 2) = vec3 0 1 0 := by
  apply exists_spatial_triangle
  norm_num [vec3, PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq]

def triangle : Triangle := exists_coordinates.choose

def basePlacement : Plane →ᵃⁱ[ℝ] Space := exists_coordinates.choose_spec.choose

theorem basePlacement_vertex (i : Fin 3) :
    basePlacement (triangle.vertex i) = ![vec3 0 0 1, vec3 1 0 0, vec3 0 1 0] i := by
  have vertices := exists_coordinates.choose_spec.choose_spec
  fin_cases i
  · exact vertices.1
  · exact vertices.2.1
  · exact vertices.2.2

def reflection (f : Bool × Bool) : Space →ₗ[ℝ] Space where
  toFun z := vec3 (sign f.1 * z 0) (sign f.2 * z 1) (z 2)
  map_add' x y := by ext i; fin_cases i <;> simp [vec3] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [vec3] <;> ring

theorem reflection_norm (f : Bool × Bool) (z : Space) : ‖reflection f z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, reflection, vec3, mul_pow]

def reflectionIsometry (f : Bool × Bool) : Space →ₗᵢ[ℝ] Space :=
  { reflection f with norm_map' := reflection_norm f }

def placement (f : Bool × Bool) : Plane →ᵃⁱ[ℝ] Space :=
  (reflectionIsometry f).toAffineIsometry.comp basePlacement

def vertex (f : Bool × Bool) (i : Fin 3) : Space :=
  ![vec3 0 0 1, vec3 (sign f.1) 0 0, vec3 0 (sign f.2) 0] i

@[simp] theorem placement_vertex (f : Bool × Bool) (i : Fin 3) :
    placement f (triangle.vertex i) = vertex f i := by
  change reflection f (basePlacement (triangle.vertex i)) = vertex f i
  rw [basePlacement_vertex]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [reflection, vec3, vertex]

/-- The three actual spatial coordinates are signed barycentric coordinates. -/
theorem placement_coordinates (f : Bool × Bool) (x : Plane) :
    placement f x = vec3 (sign f.1 * triangle.coord 1 x)
      (sign f.2 * triangle.coord 2 x) (triangle.coord 0 x) := by
  have maps (j : Fin 3) :
      (EuclideanSpace.proj j).toLinearMap.toAffineMap.comp (placement f).toAffineMap =
        ![sign f.1 • triangle.coord 1, sign f.2 • triangle.coord 2, triangle.coord 0] j := by
    apply triangle.affine_ext
    intro i
    change placement f (triangle.vertex i) j = _
    rw [placement_vertex]
    fin_cases i <;> fin_cases j <;> simp [vertex, vec3, Triangle.coord_vertex]
  ext j
  have value := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A x) (maps j)
  fin_cases j <;> exact value

end Unfoldings.Examples.Pyramid
