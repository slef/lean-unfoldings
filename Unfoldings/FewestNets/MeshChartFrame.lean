module

public import Unfoldings.FewestNets.MeshBisectors

/-! A centered gnomonic frame and derivative normalization for the finite certificate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open NormedSpace

theorem norm_sq_spatialCross (a b : Space) :
    ‖spatialCross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_eq_coordinate_dotProduct]
  change dotProduct (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))
      (crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) = _
  rw [cross_dot_cross, dotProduct_comm (WithLp.ofLp b) (WithLp.ofLp a), pow_two]

namespace MeshStar

/-- The chosen coordinate direction projected into the site's tangent plane. -/
def chartFirst (s : Space) : Space :=
  normalize (bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]))

def chartSecond (s : Space) : Space := spatialCross s (chartFirst s)

theorem chartFrame_orthonormal {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) :
    ‖chartFirst s‖ = 1 ∧ ‖chartSecond s‖ = 1 ∧
      inner ℝ s (chartFirst s) = 0 ∧ inner ℝ s (chartSecond s) = 0 ∧
      inner ℝ (chartFirst s) (chartSecond s) = 0 := by
  have first : ‖chartFirst s‖ = 1 := norm_normalize genuine
  have perpendicular : inner ℝ s (chartFirst s) = 0 := by
    rw [chartFirst, NormedSpace.normalize, real_inner_smul_right, bisectorTangent, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, unit, one_pow, mul_one, sub_self, mul_zero]
  have second : ‖chartSecond s‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    simp [chartSecond, norm_sq_spatialCross, unit, first, perpendicular]
  exact ⟨first, second, perpendicular, inner_left_spatialCross _ _, inner_right_spatialCross _ _⟩

/-- Coordinates in the two axes of the tangent plane. -/
def chartPoint (s z : Space) : Plane :=
  WithLp.toLp 2 ![inner ℝ z (chartFirst s), inner ℝ z (chartSecond s)]

variable {n : ℕ} (star : MeshStar (n + 1))

def physicalVertex (i : Fin (n + 1)) : Plane :=
  chartPoint star.direction (star.gnomonicVertex i)

def physicalSideNormal (i : Fin (n + 1)) : Plane :=
  chartPoint star.direction (normalize (bisectorTangent star.direction (star.neighborDirection i)))

def physicalSideOffset (i : Fin (n + 1)) : ℝ :=
  ‖bisectorTangent star.direction (star.neighborDirection i)‖ /
    (1 + inner ℝ star.direction (star.neighborDirection i))

/-- The two derivative lattice directions are obtained by removing the
radial component and dividing by the unnormalized site radius. -/
def relativeDirection (w : Space) : Plane :=
  chartPoint star.direction (‖star.site‖⁻¹ • bisectorTangent star.direction w)

/-- Circumradius of the triangle with corners 0 and the two derivative vectors. -/
def derivativeRadius (q : ℕ) : ℝ :=
  let u := star.relativeDirection (stepU q)
  let v := star.relativeDirection (stepV q)
  let aa := ‖u‖ ^ 2 / 2
  let bb := ‖v‖ ^ 2 / 2
  let cross := u 0 * v 1 - u 1 * v 0
  ‖(WithLp.toLp 2 ![(aa * v 1 - u 1 * bb) / cross, (u 0 * bb - aa * v 0) / cross] : Plane)‖

end MeshStar
end Unfoldings.FewestNets
