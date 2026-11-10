module

public import Unfoldings.Cone.AngularOverlap
public import Unfoldings.Geometry.ComplexTurn

/-!
# A cyclic disjoint fan makes exactly one turn

Positive consecutive cross products give exact cumulative headings. Disjoint
open positive spans rule out more than one turn, and closure rules out less.
No convex polygon, Euler count, or preassigned winding number is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Strictly positive linear combinations of two vectors. -/
def strictRayCone {E : Type*} [AddCommMonoid E] [Module ℝ E] (x y : E) : Set E :=
  {z | ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 < b ∧ z = a • x + b • y}

namespace AngularFan

variable {n : ℕ} (A : AngularFan n) (ray : Fin (n + 1) → ℂ)
  (angles : ∀ i, InnerProductGeometry.angle (ray i) (ray (finRotate (n + 1) i)) = A.angle i)
  (positive : ∀ i, 0 < (starRingEnd ℂ (ray i) * ray (finRotate (n + 1) i)).im)

include positive in
theorem cyclic_ray_ne_zero (i : Fin (n + 1)) : ray i ≠ 0 := by
  intro zero
  have cross := positive i
  rw [zero] at cross
  simp at cross

include angles positive

/-- These headings include the initial ray argument and retain all subsequent full turns. -/
theorem cyclic_ray_heading (i : Fin (n + 1)) :
    ray i = (‖ray i‖ : ℂ) * polarRay ((ray 0).arg + A.heading i.castSucc) := by
  refine Fin.induction ?_ (fun k previous => ?_) i
  · change ray 0 = (‖ray 0‖ : ℂ) * polarRay ((ray 0).arg + A.heading 0)
    rw [A.heading_zero, add_zero]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  · have successor := polar_successor_of_positive_cross
      ((ray 0).arg + A.heading k.castSucc.castSucc) previous (positive k.castSucc)
    rw [angles] at successor
    have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
    rw [rotated, add_assoc, ← A.heading_succ, Fin.succ_castSucc] at successor
    exact successor

theorem cyclic_ray_heading_finish (i : Fin (n + 1)) :
    ray (finRotate (n + 1) i) = (‖ray (finRotate (n + 1) i)‖ : ℂ) *
      polarRay ((ray 0).arg + A.heading i.succ) := by
  have successor := polar_successor_of_positive_cross _
    (A.cyclic_ray_heading ray angles positive i) (positive i)
  rw [angles] at successor
  simpa only [A.heading_succ, add_assoc] using successor

theorem cyclic_outer_ray : polarRay A.totalAngle = 1 := by
  have terminal := A.cyclic_ray_heading_finish ray angles positive (Fin.last n)
  rw [finRotate_last, show (Fin.last n).succ = Fin.last (n + 1) from rfl,
    A.heading_last, polarRay_add] at terminal
  have first : ray 0 = (‖ray 0‖ : ℂ) * polarRay (ray 0).arg :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  rw [← mul_assoc, ← first] at terminal
  exact mul_left_cancel₀ (cyclic_ray_ne_zero ray positive 0)
    (by simpa only [mul_one] using terminal.symm)

/-- Rotate an angular-fan sector back into the corresponding actual ray cone. -/
theorem cyclic_interior_in_cone (i : Fin (n + 1)) {z : ℂ}
    (inside : z ∈ interior (A.faceImage i)) :
    polarRay (ray 0).arg * z ∈ strictRayCone (ray i) (ray (finRotate (n + 1) i)) := by
  obtain ⟨r, rpos, θ, bounds, rfl⟩ := (A.mem_interior_faceImage_iff i z).mp inside
  have small : (ray 0).arg + A.heading i.succ -
      ((ray 0).arg + A.heading i.castSucc) < Real.pi := by
    rw [A.heading_succ]
    linarith [A.small i]
  have between : (ray 0).arg + θ ∈ Set.Ioo ((ray 0).arg + A.heading i.castSucc)
      ((ray 0).arg + A.heading i.succ) := by
    constructor <;> linarith [bounds.1, bounds.2]
  obtain ⟨a, apos, b, bpos, expression⟩ := polarRay_mem_strict_positive_span _ _ _ small between
  have first_norm : 0 < ‖ray i‖ := norm_pos_iff.mpr (cyclic_ray_ne_zero ray positive i)
  have last_norm : 0 < ‖ray (finRotate (n + 1) i)‖ :=
    norm_pos_iff.mpr (cyclic_ray_ne_zero ray positive _)
  have first : polarRay ((ray 0).arg + A.heading i.castSucc) = ‖ray i‖⁻¹ • ray i := by
    have scaled := congrArg (fun z : ℂ => ‖ray i‖⁻¹ • z)
      (A.cyclic_ray_heading ray angles positive i)
    simpa only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ first_norm.ne', Complex.ofReal_one, one_mul] using scaled.symm
  have last : polarRay ((ray 0).arg + A.heading i.succ) =
      ‖ray (finRotate (n + 1) i)‖⁻¹ • ray (finRotate (n + 1) i) := by
    have scaled := congrArg (fun z : ℂ => ‖ray (finRotate (n + 1) i)‖⁻¹ • z)
      (A.cyclic_ray_heading_finish ray angles positive i)
    simpa only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ last_norm.ne', Complex.ofReal_one, one_mul] using scaled.symm
  rw [first, last] at expression
  refine ⟨r * a * ‖ray i‖⁻¹, mul_pos (mul_pos rpos apos) (inv_pos.mpr first_norm),
    r * b * ‖ray (finRotate (n + 1) i)‖⁻¹,
    mul_pos (mul_pos rpos bpos) (inv_pos.mpr last_norm), ?_⟩
  calc
    polarRay (ray 0).arg * ((r : ℂ) * polarRay θ) =
        r • polarRay ((ray 0).arg + θ) := by rw [polarRay_add, Complex.real_smul]; ring
    _ = _ := by rw [expression]; simp only [smul_add, smul_smul, mul_assoc]

/-- An actual cyclic fan of disjoint convex wedges has precisely one full turn. -/
theorem totalAngle_eq_two_pi_of_cyclic_rays
    (separated : Pairwise (fun i j => Disjoint
      (strictRayCone (ray i) (ray (finRotate (n + 1) i)))
      (strictRayCone (ray j) (ray (finRotate (n + 1) j))))) :
    A.totalAngle = 2 * Real.pi := by
  have nonoverlap : A.Nonoverlapping := by
    intro i j different
    apply Set.disjoint_left.mpr
    intro z first last
    exact Set.disjoint_left.mp (separated different)
      (A.cyclic_interior_in_cone ray angles positive i first)
      (A.cyclic_interior_in_cone ray angles positive j last)
  have upper := A.nonoverlapping_iff_totalAngle_le.mp nonoverlap
  have circle : Circle.exp A.totalAngle = 1 := by
    apply Subtype.ext
    exact A.cyclic_outer_ray ray angles positive
  obtain ⟨k, turns⟩ := Circle.exp_eq_one.mp circle
  have kpos : 0 < (k : ℝ) := by nlinarith [A.totalAngle_pos, Real.pi_pos]
  have kle : (k : ℝ) ≤ 1 := by nlinarith [Real.pi_pos]
  have integer_positive : 0 < k := by exact_mod_cast kpos
  have integer_bound : k ≤ 1 := by exact_mod_cast kle
  have one : k = 1 := by omega
  rw [one] at turns
  simpa only [Int.cast_one, one_mul] using turns

end AngularFan
end Unfoldings
