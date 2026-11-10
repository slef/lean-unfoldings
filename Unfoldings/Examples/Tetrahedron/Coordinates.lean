module

public import Unfoldings.Geometry.Barycentric
public import Unfoldings.Complex.Folding
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Coordinates for a concrete tetrahedron

The vertices are `(0,0,0)`, `(1,0,0)`, `(1,1,0)`, `(1,1,1)`.
Face `f` omits vertex `f`; its planar corners list the other vertices in
increasing order. The two diagonal faces use orthonormal coordinates.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

def vec2 (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

def vec3 (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

def vertex : Fin 4 → Space := ![0, vec3 1 0 0, vec3 1 1 0, vec3 1 1 1]

def corner : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

def linear (f : Fin 4) : Plane →ₗ[ℝ] Space where
  toFun x := match f with
    | 0 => vec3 0 (x 0) (x 1)
    | 1 => vec3 (x 0 / Real.sqrt 2) (x 0 / Real.sqrt 2) (x 1)
    | 2 => vec3 (x 0) (x 1 / Real.sqrt 2) (x 1 / Real.sqrt 2)
    | 3 => vec3 (x 0) (x 1) 0
  map_add' x y := by
    fin_cases f <;> ext i <;> fin_cases i <;> simp [vec3] <;> ring
  map_smul' c x := by
    fin_cases f <;> ext i <;> fin_cases i <;> simp [vec3] <;> ring

theorem norm_linear (f : Fin 4) (x : Plane) : ‖linear f x‖ = ‖x‖ := by
  have root : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have nonzero : Real.sqrt 2 ≠ 0 := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  fin_cases f <;>
    simp [linear, vec3, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

def linearIsometry (f : Fin 4) : Plane →ₗᵢ[ℝ] Space :=
  { toLinearMap := linear f, norm_map' := norm_linear f }

def placement (f : Fin 4) : Plane →ᵃⁱ[ℝ] Space :=
  (AffineIsometryEquiv.vaddConst ℝ (if f = 0 then vec3 1 0 0 else 0)).toAffineIsometry.comp
    (linearIsometry f).toAffineIsometry

def triangle (f : Fin 4) : Triangle where
  vertex := match f with
    | 0 => ![0, vec2 1 0, vec2 1 1]
    | 1 => ![0, vec2 (Real.sqrt 2) 0, vec2 (Real.sqrt 2) 1]
    | 2 => ![0, vec2 1 0, vec2 1 (Real.sqrt 2)]
    | 3 => ![0, vec2 1 0, vec2 1 1]
  nondegenerate := by
    have root : Real.sqrt 2 ≠ 0 := by positivity
    fin_cases f <;> simp [orient, vec2, root]

theorem placement_vertex (f : Fin 4) (i : Fin 3) :
    placement f ((triangle f).vertex i) = vertex (corner f i) := by
  have root : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases f <;> fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [placement, linearIsometry, linear, triangle, vertex, corner,
      AffineIsometryEquiv.vaddConst, vec2, vec3, root]

theorem sum_vertex (i : Fin 4) : ∑ j, vertex i j = (i.val : ℝ) := by
  fin_cases i <;> norm_num [vertex, vec3, Fin.sum_univ_succ]

theorem vertex_injective : Function.Injective vertex := by
  intro i j equal
  have sum := congrArg (fun x : Space => ∑ k, x k) equal
  rw [sum_vertex, sum_vertex] at sum
  exact Fin.ext (by exact_mod_cast sum)

theorem placement_image_carrier (f : Fin 4) :
    placement f '' (triangle f).carrier = convexHull ℝ (Set.range (vertex ∘ corner f)) := by
  change (placement f).toAffineMap '' convexHull ℝ (Set.range (triangle f).vertex) = _
  rw [(placement f).toAffineMap.image_convexHull]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  exact placement_vertex f i

end Unfoldings.Examples.Tetrahedron
