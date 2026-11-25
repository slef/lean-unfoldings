module

public import Unfoldings.Convex.PolygonSideDirections
public import Unfoldings.Geometry.AcuteHeadingControls
public import Mathlib.Algebra.Order.Floor.Semiring

/-! A finite family of equally spaced supporting halfplanes forms a centered regular selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

variable (frame : Plane ≃ₗᵢ[ℝ] ℂ)

/-- The outward normal halfway between consecutive vertex longitudes. -/
def regularSideNormal {k : ℕ} (i : Fin k) : Plane :=
  frame.symm (polarRay ((2 * i.val + 1) * (π / k)))

/-- The regular selector with circumradius radius and k sides. -/
def regularSlopePolygon (k : ℕ) (radius : ℝ) : Set Plane :=
  {p | ∀ i : Fin k, inner ℝ (regularSideNormal frame i) p ≤ radius * cos (π / k)}

private theorem regular_half_step_pos {k : ℕ} (sides : 3 ≤ k) : 0 < π / (k : ℝ) :=
  div_pos pi_pos (Nat.cast_pos.mpr (by omega))

private theorem regular_half_step_le {k : ℕ} (sides : 3 ≤ k) : π / (k : ℝ) ≤ π / 3 :=
  div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by exact_mod_cast sides)

/-- The support directions have the exact common apothem and the origin as
their strict reference. -/
def regularPolygonSideDirections {k : ℕ} (sides : 3 ≤ k) {radius : ℝ} (positive : 0 < radius) :
    PolygonSideDirections (Fin k) (regularSlopePolygon frame k radius) where
  normal := regularSideNormal frame
  offset := fun _ => radius * cos (π / k)
  unit := fun i => (frame.symm.norm_map _).trans (norm_polarRay _)
  reference := 0
  strict := fun _ => by
    rw [inner_zero_right]
    exact mul_pos positive (cos_pos_of_mem_Ioo
      ⟨by linarith only [regular_half_step_pos sides, pi_pos],
        by linarith only [regular_half_step_le sides, pi_pos]⟩)
  carrier_eq := rfl

/-- A point on any ray sees a side normal within a half step. Its corresponding
support inequality puts the full polygon inside its circumdisk. -/
theorem norm_le_of_mem_regularSlopePolygon {k : ℕ} (sides : 3 ≤ k) {radius : ℝ}
    {p : Plane} (member : p ∈ regularSlopePolygon frame k radius) : ‖p‖ ≤ radius := by
  let x := π / (k : ℝ)
  have x_pos : 0 < x := regular_half_step_pos sides
  have x_le : x ≤ π / 3 := regular_half_step_le sides
  have two_pos : 0 < 2 * x := by positivity
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have period : (k : ℝ) * (2 * x) = 2 * π := by
    dsimp only [x]
    field_simp [k_pos.ne'] <;> ring
  let arg := (frame p).arg
  let θ := if arg < 0 then arg + 2 * π else arg
  have θ_range : 0 ≤ θ ∧ θ < 2 * π := by
    unfold θ
    split_ifs with h
    · exact ⟨by linarith only [Complex.neg_pi_lt_arg (frame p), pi_pos], by linarith only [h]⟩
    · exact ⟨le_of_not_gt h, by linarith only [Complex.arg_le_pi (frame p), pi_pos]⟩
  let index := ⌊θ / (2 * x)⌋₊
  have within : index < k := by
    apply (Nat.floor_lt (div_nonneg θ_range.1 two_pos.le)).2
    exact (div_lt_iff₀ two_pos).2 (period.symm ▸ θ_range.2)
  let i : Fin k := ⟨index, within⟩
  let phase := (2 * (index : ℝ) + 1) * x
  have earliest := (le_div_iff₀ two_pos).mp (Nat.floor_le (div_nonneg θ_range.1 two_pos.le))
  have latest := (div_lt_iff₀ two_pos).mp (Nat.lt_floor_add_one (θ / (2 * x)))
  have close : |θ - phase| ≤ x := by
    apply abs_le.mpr
    constructor <;> dsimp only [phase, index] <;> linarith only [earliest, latest]
  have cos_same : cos (θ - phase) = cos (arg - phase) := by
    unfold θ
    split_ifs
    · rw [show arg + 2 * π - phase = (arg - phase) + 2 * π by ring, cos_add_two_pi]
    · rfl
  have cosine : cos x ≤ cos (arg - phase) := calc
    _ ≤ cos |θ - phase| :=
      cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith only [x_le, pi_pos]) close
    _ = _ := (cos_abs _).trans cos_same
  have height : ‖p‖ * cos (arg - phase) ≤ radius * cos x := by
    have h := member i
    change headingControl frame phase p ≤ radius * cos x at h
    rw [headingControl_apply] at h
    exact h
  have cos_pos : 0 < cos x := cos_pos_of_mem_Ioo
    ⟨by linarith only [x_pos, pi_pos], by linarith only [x_le, pi_pos]⟩
  exact (mul_le_mul_iff_of_pos_right cos_pos).mp
    ((mul_le_mul_of_nonneg_left cosine (norm_nonneg p)).trans height)

end Unfoldings
