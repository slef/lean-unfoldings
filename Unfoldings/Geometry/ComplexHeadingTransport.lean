module

public import Unfoldings.Geometry.ComplexTurn
public import Unfoldings.Geometry.ChainConstruction
public import Mathlib.Analysis.Complex.Angle

/-!
# Real heading transport with signed phase corrections

The local residual angle is chosen in the principal interval. Its absolute value
is the genuine angular distance after removing the prescribed phase. Adding
these real residuals and phases constructs unreduced headings along the whole
finite sequence; signed phases are summed before taking absolute values.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Complex normalization respects multiplication, including zero factors. -/
theorem complex_normalize_mul (x y : ℂ) :
    NormedSpace.normalize (x * y) = NormedSpace.normalize x * NormedSpace.normalize y := by
  simp only [NormedSpace.normalize, Complex.real_smul, norm_mul, mul_inv,
    Complex.ofReal_mul]
  ring

/-- The actual normalized direction is its principal argument's unit ray. -/
theorem complex_normalize_eq_polar_arg {x : ℂ} (nonzero : x ≠ 0) :
    NormedSpace.normalize x = polarRay x.arg := by
  have polar := (Complex.norm_mul_exp_arg_mul_I x).symm
  change x = (‖x‖ : ℂ) * polarRay x.arg at polar
  unfold NormedSpace.normalize
  rw [Complex.real_smul]
  conv_lhs => arg 2; rw [polar]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero),
    Complex.ofReal_one, one_mul]

/-- A real signed residual realizes an actual direction transition after phase removal. -/
theorem exists_complex_phase_residual {x y : ℂ} (xne : x ≠ 0) (yne : y ≠ 0) (κ : ℝ) :
    ∃ δ : ℝ,
      |δ| = InnerProductGeometry.angle x (polarRay (-κ) * y) ∧
      NormedSpace.normalize y = polarRay (κ + δ) * NormedSpace.normalize x := by
  let z := polarRay (-κ) * y
  have zne : z ≠ 0 := mul_ne_zero (polarRay_ne_zero _) yne
  let δ := (z / x).arg
  have angle : |δ| = InnerProductGeometry.angle x z := by
    rw [InnerProductGeometry.angle_comm x z, Complex.angle_eq_abs_arg zne xne]
  have step : NormedSpace.normalize z = polarRay δ * NormedSpace.normalize x := by
    calc
      _ = NormedSpace.normalize ((z / x) * x) := by rw [div_mul_cancel₀ _ xne]
      _ = _ := by
        rw [complex_normalize_mul, complex_normalize_eq_polar_arg (div_ne_zero zne xne)]
  have undo : polarRay κ * z = y := by
    change polarRay κ * (polarRay (-κ) * y) = y
    rw [← mul_assoc, ← polarRay_add, add_neg_cancel, polarRay_zero, one_mul]
  have normalized : NormedSpace.normalize (polarRay κ * z) =
      polarRay κ * NormedSpace.normalize z := by
    rw [complex_normalize_mul]
    simp only [NormedSpace.normalize, norm_polarRay, inv_one, one_smul]
  refine ⟨δ, angle, ?_⟩
  rw [← undo, normalized, step, polarRay_add, mul_assoc]

/-- Compose all actual phase-corrected directions with a real, unreduced heading bound. -/
theorem exists_complex_heading_transport {n : ℕ} (direction : Fin (n + 1) → ℂ)
    (genuine : ∀ i, direction i ≠ 0) (phase bend : Fin n → ℝ)
    (local_bound : ∀ i, InnerProductGeometry.angle (direction i.castSucc)
      (polarRay (-phase i) * direction i.succ) ≤ bend i) :
    ∃ heading : Fin (n + 1) → ℝ,
      heading 0 = (direction 0).arg ∧
      (∀ i, NormedSpace.normalize (direction i) = polarRay (heading i)) ∧
      |heading (Fin.last n) - heading 0 - ∑ i, phase i| ≤ ∑ i, bend i := by
  choose residual magnitude step using
    (fun i : Fin n => exists_complex_phase_residual
      (genuine i.castSucc) (genuine i.succ) (phase i))
  let heading (i : Fin (n + 1)) :=
    (direction 0).arg + Fin.partialSum phase i + Fin.partialSum residual i
  have first : heading 0 = (direction 0).arg := by
    simp only [heading, Fin.partialSum_zero, add_zero]
  have realizes (i : Fin (n + 1)) :
      NormedSpace.normalize (direction i) = polarRay (heading i) := by
    refine Fin.induction ?_ (fun k previous => ?_) i
    · rw [first]
      exact complex_normalize_eq_polar_arg (genuine 0)
    · rw [step k, previous, ← polarRay_add]
      congr 1
      simp only [heading, Fin.partialSum_succ]
      ring
  have total (weight : Fin n → ℝ) : Fin.partialSum weight (Fin.last n) = ∑ i, weight i := by
    change ((List.ofFn weight).take n).sum = ∑ i, weight i
    rw [List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl), List.sum_ofFn]
  refine ⟨heading, first, realizes, ?_⟩
  have difference : heading (Fin.last n) - heading 0 - ∑ i, phase i = ∑ i, residual i := by
    rw [first]
    simp only [heading, total]
    ring
  rw [difference]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => (magnitude i).trans_le (local_bound i)))

end Unfoldings
