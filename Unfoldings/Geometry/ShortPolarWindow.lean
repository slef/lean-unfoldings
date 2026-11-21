module

public import Unfoldings.Geometry.ComplexHeadingTransport
public import Unfoldings.Geometry.PolarAngleBound
public import Unfoldings.Geometry.PlanePolarWindow

/-! A finite polar window of variation below a half-turn has a common acute axis. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

private theorem abs_partialSum_sub_le_sum_abs {n : ℕ} (weight : Fin n → ℝ)
    (i j : Fin (n + 1)) (order : i ≤ j) :
    |Fin.partialSum weight j - Fin.partialSum weight i| ≤ ∑ k, |weight k| := by
  classical
  have difference : Fin.partialSum weight j - Fin.partialSum weight i =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < j.val), weight k := by
    simp only [Fin.partialSum, List.sum_take_ofFn, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases inside : k.val < i.val
    · have later : k.val < j.val := inside.trans_le order
      simp only [inside, later, ite_true, sub_self, not_le.mpr inside, false_and, ite_false]
    · have outside : i.val ≤ k.val := le_of_not_gt inside
      simp only [inside, outside, ite_false, sub_zero, true_and]
  rw [difference]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => abs_nonneg _))

/-- The actual angular variation can be arbitrarily close to π. Every ray
still lies within a strict right angle of one common direction. -/
theorem exists_acute_axis_of_short_polar_window {n : ℕ} (ray : Fin (n + 1) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (short : (∑ k : Fin n, angle (ray k.castSucc) (ray k.succ)) < π) :
    ∃ axis : Plane, axis ≠ 0 ∧ ∀ i, angle axis (ray i) < π / 2 := by
  classical
  let frame : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let z (i : Fin (n + 1)) := frame (ray i)
  have nonzero (i) : z i ≠ 0 := by
    intro eq
    exact genuine i (frame.injective (eq.trans (map_zero frame).symm))
  choose turn size step using fun k : Fin n =>
    exists_complex_phase_residual (nonzero k.castSucc) (nonzero k.succ) 0
  let phase (i : Fin (n + 1)) := (z 0).arg + Fin.partialSum turn i
  have presents (i : Fin (n + 1)) : NormedSpace.normalize (z i) = polarRay (phase i) := by
    refine Fin.induction ?_ (fun k previous => ?_) i
    · simpa only [phase, Fin.partialSum_zero, add_zero] using
        complex_normalize_eq_polar_arg (nonzero 0)
    · rw [step k, previous, ← polarRay_add]
      congr 1
      simp only [phase, Fin.partialSum_succ]
      ring
  have sum_eq : (∑ k, |turn k|) = ∑ k : Fin n, angle (ray k.castSucc) (ray k.succ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [size k, neg_zero, polarRay_zero, one_mul]
    exact frame.toLinearIsometry.angle_map _ _
  have spread (i j : Fin (n + 1)) : |phase j - phase i| < π := by
    change |(z 0).arg + Fin.partialSum turn j - ((z 0).arg + Fin.partialSum turn i)| < π
    rw [add_sub_add_left_eq_sub]
    rcases le_total i j with forward | backward
    · exact (abs_partialSum_sub_le_sum_abs turn i j forward).trans_lt (sum_eq ▸ short)
    · rw [abs_sub_comm]
      exact (abs_partialSum_sub_le_sum_abs turn j i backward).trans_lt (sum_eq ▸ short)
  obtain ⟨lo, _, minimum⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1)))
    phase Finset.univ_nonempty
  obtain ⟨hi, _, maximum⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    phase Finset.univ_nonempty
  let center := (phase hi + phase lo) / 2
  let axis := frame.symm (polarRay center)
  have genuine_axis : axis ≠ 0 := by
    intro zero
    exact polarRay_ne_zero center (by
      simpa only [axis, frame.apply_symm_apply, map_zero] using congrArg frame zero)
  refine ⟨axis, genuine_axis, ?_⟩
  intro i
  have total := spread lo hi
  have below := minimum i (Finset.mem_univ i)
  have above := maximum i (Finset.mem_univ i)
  have difference : |phase i - center| < π / 2 := by
    have width := (abs_lt.mp total).2
    apply abs_lt.mpr
    dsimp [center]
    constructor <;> linarith only [width, below, above]
  have angle := angle_polarRay_le_abs_sub center (phase i)
  rw [← presents i, angle_normalize_right] at angle
  have change_frame := frame.toLinearIsometry.angle_map axis (ray i)
  change InnerProductGeometry.angle (frame (frame.symm (polarRay center))) (z i) =
    InnerProductGeometry.angle axis (ray i) at change_frame
  rw [frame.apply_symm_apply] at change_frame
  rw [← change_frame]
  exact angle.trans_lt difference

end Unfoldings
