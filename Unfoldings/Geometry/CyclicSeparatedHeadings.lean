module

public import Unfoldings.Geometry.ConvexChordTurns
public import Unfoldings.Combinatorics.CyclicHeadingReindex

/-! One positive turn of rays gives separated real headings in a single period. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real
open scoped BigOperators
attribute [local instance] Complex.finrank_real_complex_fact

private theorem polarRay_sub_full_turn (x : ℝ) : polarRay (x - 2 * π) = polarRay x := by
  apply Complex.ext
  · simp only [polarRay_re, Real.cos_sub_two_pi]
  · simp only [polarRay_im, Real.sin_sub_two_pi]

/-- The initial index of a positively oriented cycle can be chosen so that
its arguments increase through one period with the given minimum gaps. -/
theorem exists_separated_cyclic_ray_headings {n : ℕ} (ray : Fin (n + 1) → ℂ)
    {eta : ℝ} (eta_pos : 0 < eta)
    (minimum : ∀ i, eta ≤ angle (ray i) (ray (finRotate (n + 1) i)))
    (turns : ∀ i, 0 < Complex.orientation.areaForm (ray i) (ray (finRotate (n + 1) i)))
    (total : (∑ i, angle (ray i) (ray (finRotate (n + 1) i))) = 2 * π) :
    ∃ (start : Fin (n + 1)) (head : Fin (n + 1) → ℝ),
      (∀ i, 0 ≤ head i ∧ head i < 2 * π) ∧
      (∀ i j, i < j → eta ≤ head j - head i ∧ head j - head i ≤ 2 * π - eta) ∧
      ∀ i, ray (i + start) = (‖ray (i + start)‖ : ℂ) * polarRay (head i) := by
  let next := finRotate (n + 1)
  have short (i : Fin (n + 1)) : angle (ray i) (ray (next i)) < π := by
    apply lt_of_le_of_ne (angle_le_pi _ _)
    intro eq
    obtain ⟨r, _, h⟩ := (angle_eq_pi_iff.mp eq).2
    have pos := turns i
    change 0 < Complex.orientation.areaForm (ray i) (ray (next i)) at pos
    rw [h, map_smul, Complex.orientation.areaForm_apply_self, smul_zero] at pos
    exact (lt_irrefl (0 : ℝ)) pos
  let A : AngularFan n :=
    ⟨fun i => angle (ray i) (ray (next i)), fun i => eta_pos.trans_le (minimum i), short⟩
  have full : A.totalAngle = 2 * π := total
  let base := (ray 0).arg
  let anchor := if base < 0 then base + 2 * π else base
  have anchor_range : 0 ≤ anchor ∧ anchor < 2 * π := by
    have lo := Complex.neg_pi_lt_arg (ray 0)
    have hi := Complex.arg_le_pi (ray 0)
    by_cases neg : base < 0
    · rw [show anchor = base + 2 * π from ite_eq_left neg]
      constructor <;> linarith [pi_pos]
    · rw [show anchor = base from ite_eq_right neg]
      exact ⟨le_of_not_gt neg, by linarith [pi_pos]⟩
  let H (i : Fin (n + 1)) := anchor + A.heading i.castSucc
  have head_range (i : Fin (n + 1)) : 0 ≤ H i ∧ H i < 2 * (2 * π) := by
    have h := A.heading_le_totalAngle i.castSucc
    rw [full] at h
    exact ⟨add_nonneg anchor_range.1 (A.heading_nonneg _), by dsimp [H]; linarith [anchor_range.2]⟩
  have gap (i j : Fin (n + 1)) (ij : i < j) :
      eta ≤ H j - H i ∧ H j - H i ≤ 2 * π - eta := by
    have after : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      omega
    have lower := A.heading_strictMono.monotone after
    rw [A.heading_succ] at lower
    have before_last : j.castSucc ≤ (Fin.last n).castSucc := by
      exact Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)
    have upper := A.heading_strictMono.monotone before_last
    have last := A.heading_succ (Fin.last n)
    rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl, A.heading_last, full] at last
    have step_le (k : Fin (n + 1)) : eta ≤ A.angle k := minimum k
    dsimp only [H]
    constructor
    · linarith only [lower, step_le i]
    · linarith only [upper, A.heading_nonneg i.castSucc, last, step_le (Fin.last n)]
  have phase (i : Fin (n + 1)) : ray i = (‖ray i‖ : ℂ) * polarRay (H i) := by
    have eq := A.cyclic_ray_heading ray (fun _ => rfl) (fun j => by
      rw [← Complex.areaForm]
      exact turns j) i
    by_cases neg : base < 0
    · have shifted : H i - 2 * π = base + A.heading i.castSucc := by
        dsimp only [H, anchor]
        rw [ite_eq_left neg]
        ring
      rw [← polarRay_sub_full_turn (H i), shifted]
      exact eq
    · have same : H i = base + A.heading i.castSucc := by
        exact congrArg (· + A.heading i.castSucc) (ite_eq_right neg)
      rw [same]
      exact eq
  obtain ⟨start, h, bounds, gaps, period⟩ :=
    exists_cyclic_heading_reindex H eta_pos head_range gap
  refine ⟨start, h, bounds, gaps, fun i => ?_⟩
  conv_lhs => rw [phase]
  rcases period i with same | change
  · rw [same]
  · rw [← change]
    have full_turn := polarRay_sub_full_turn (h i + 2 * π)
    rw [add_sub_cancel_right] at full_turn
    rw [full_turn]

end Unfoldings
