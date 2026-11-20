module

public import Unfoldings.Geometry.CyclicRays
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-! A supported convex chord chain makes exactly one turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry
open scoped BigOperators
attribute [local instance] Complex.finrank_real_complex_fact

private theorem angle_genuine_of_areaForm_pos {u v : ℂ}
    (positive : 0 < Complex.orientation.areaForm u v) :
    0 < angle u v ∧ angle u v < Real.pi := by
  have axis {r : ℝ} (same : v = r • u) : False := by
    rw [same, map_smul, Complex.orientation.areaForm_apply_self, smul_zero] at positive
    exact (lt_irrefl _) positive
  exact ⟨lt_of_le_of_ne (angle_nonneg _ _) fun zero =>
    axis (angle_eq_zero_iff.mp zero.symm).2.choose_spec.2,
    lt_of_le_of_ne (angle_le_pi _ _) fun pi =>
      axis (angle_eq_pi_iff.mp pi).2.choose_spec.2⟩

private theorem eq_zero_of_areaForm_zero_left {u v w : ℂ}
    (positive : 0 < Complex.orientation.areaForm u v)
    (uw : Complex.orientation.areaForm u w = 0)
    (vw : Complex.orientation.areaForm v w = 0) : w = 0 := by
  have orthogonal := Complex.orientation.inner_mul_areaForm_sub u v w
  rw [uw, vw, mul_zero, zero_sub, mul_zero, neg_eq_zero] at orthogonal
  have dot := (mul_eq_zero.mp orthogonal).resolve_left positive.ne'
  have norm := Complex.orientation.inner_sq_add_areaForm_sq u w
  rw [uw, dot, zero_pow (by decide), add_zero] at norm
  have u_ne : ‖u‖ ≠ 0 := by
    intro zero
    have u_zero := norm_eq_zero.mp zero
    simp [u_zero] at positive
  have sq : ‖w‖ ^ 2 = 0 := (mul_eq_zero.mp norm.symm).resolve_left (pow_ne_zero _ u_ne)
  exact norm_eq_zero.mp ((mul_eq_zero.mp (by simpa only [pow_two] using sq)).elim id id)

variable {n : ℕ} (p : Fin (n + 1) → ℂ)

private def chord (i : Fin (n + 1)) : ℂ := p (finRotate (n + 1) i) - p i

private theorem areaForm_chord_to_next (i j : Fin (n + 1)) :
    Complex.orientation.areaForm (chord p i) (p j - p (finRotate (n + 1) i)) =
      Complex.orientation.areaForm (chord p i) (p j - p i) := by
  rw [show p j - p (finRotate (n + 1) i) = (p j - p i) - chord p i by
    dsimp [chord]; abel]
  rw [map_sub, Complex.orientation.areaForm_apply_self, sub_zero]

private theorem disjoint_chord_turn_cones (injective : Function.Injective p)
    (supports : ∀ i j, 0 ≤ Complex.orientation.areaForm (chord p i) (p j - p i))
    (positive : ∀ i,
      0 < Complex.orientation.areaForm (chord p i) (chord p (finRotate (n + 1) i))) :
    Pairwise (fun i j => Disjoint
      (strictRayCone (chord p i) (chord p (finRotate (n + 1) i)))
      (strictRayCone (chord p j) (chord p (finRotate (n + 1) j)))) := by
  let next := finRotate (n + 1)
  have compare (i k : Fin (n + 1)) {z : ℂ}
      (hz : z ∈ strictRayCone (chord p i) (chord p (next i))) :
      0 ≤ Complex.orientation.areaForm z (p k - p (next i)) := by
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, areaForm_chord_to_next p i k]
    exact add_nonneg (mul_nonneg ha.le (supports i k))
      (mul_nonneg hb.le (supports (next i) k))
  intro i j hne
  apply Set.disjoint_left.mpr
  intro z hi hj
  let direction := p (next j) - p (next i)
  have first := compare i (next j) hi
  have last := compare j (next i) hj
  change 0 ≤ Complex.orientation.areaForm z direction at first
  have reverse : p (next i) - p (next j) = -direction := by dsimp [direction]; abel
  rw [reverse, map_neg] at last
  have zero : Complex.orientation.areaForm z direction = 0 := by linarith
  obtain ⟨a, ha, b, hb, rfl⟩ := hi
  have first_i : 0 ≤ Complex.orientation.areaForm (chord p i) direction := by
    change 0 ≤ Complex.orientation.areaForm (chord p i) (p (next j) - p (next i))
    rw [areaForm_chord_to_next]
    exact supports i (next j)
  have first_next : 0 ≤ Complex.orientation.areaForm (chord p (next i)) direction :=
    supports (next i) (next j)
  rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at zero
  have h₁ : Complex.orientation.areaForm (chord p i) direction = 0 := by
    by_contra ne
    have pos := mul_pos ha (lt_of_le_of_ne first_i (Ne.symm ne))
    linarith only [zero, pos, mul_nonneg hb.le first_next]
  have h₂ : Complex.orientation.areaForm (chord p (next i)) direction = 0 := by
    by_contra ne
    have pos := mul_pos hb (lt_of_le_of_ne first_next (Ne.symm ne))
    linarith only [zero, pos, mul_nonneg ha.le first_i]
  have same := eq_zero_of_areaForm_zero_left (positive i) h₁ h₂
  exact hne (next.injective (injective (sub_eq_zero.mp same)).symm)

/-- The exterior turns of a convex chord chain sum to one complete turn.
The signed support inequalities refer only to its vertices, so this applies
to chords inscribed in a convex region with curved sides as well. -/
theorem sum_convex_chord_turns_eq_two_pi (injective : Function.Injective p)
    (supports : ∀ i j, 0 ≤ Complex.orientation.areaForm
      (p (finRotate (n + 1) i) - p i) (p j - p i))
    (positive : ∀ i, 0 < Complex.orientation.areaForm
      (p (finRotate (n + 1) i) - p i)
      (p (finRotate (n + 1) (finRotate (n + 1) i)) - p (finRotate (n + 1) i))) :
    (∑ i, angle (p (finRotate (n + 1) i) - p i)
        (p (finRotate (n + 1) (finRotate (n + 1) i)) - p (finRotate (n + 1) i))) =
      2 * Real.pi := by
  let A : AngularFan n :=
    ⟨fun i => angle (chord p i) (chord p (finRotate (n + 1) i)),
      fun i => (angle_genuine_of_areaForm_pos (positive i)).1,
      fun i => (angle_genuine_of_areaForm_pos (positive i)).2⟩
  apply A.totalAngle_eq_two_pi_of_cyclic_rays (chord p) (fun _ => rfl)
  · intro i
    rw [← Complex.areaForm]
    exact positive i
  · exact disjoint_chord_turn_cones p injective supports positive

end Unfoldings
