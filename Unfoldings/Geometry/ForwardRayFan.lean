module

public import Unfoldings.Geometry.SignedPlanarAngle
public import Unfoldings.Geometry.HalfplaneFan

/-! A consistently ordered fan in the forward halfplane has total angle at most π. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

theorem signedPlanarAngle_eq_arg_sub_of_halfplane {p q : Plane}
    (pn : p ≠ 0) (qn : q ≠ 0) (px : 0 ≤ p 0) (qx : 0 ≤ q 0)
    (noncollinear : orient 0 p q ≠ 0) :
    signedPlanarAngle p q = (orientedComplex q).arg - (orientedComplex p).arg := by
  let Z := orientedComplex p
  let W := orientedComplex q
  have z0 : 0 ≤ Z.re := by simpa only [Z, orientedComplex_re] using px
  have w0 : 0 ≤ W.re := by simpa only [W, orientedComplex_re] using qx
  have zb : Z.arg ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl z0), Complex.arg_le_pi_div_two_iff.mpr (Or.inl z0)⟩
  have wb : W.arg ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl w0), Complex.arg_le_pi_div_two_iff.mpr (Or.inl w0)⟩
  have lower : -π < W.arg - Z.arg := by
    by_contra! fail
    have zh : Z.arg = π / 2 := by linarith only [fail, wb.1, zb.2]
    have wh : W.arg = -(π / 2) := by linarith only [fail, wb.1, zb.2]
    have zr := (Complex.arg_eq_pi_div_two_iff.mp zh).1
    have wr := (Complex.arg_eq_neg_pi_div_two_iff.mp wh).1
    change (orientedComplex p).re = 0 at zr
    change (orientedComplex q).re = 0 at wr
    rw [orientedComplex_re] at zr wr
    apply noncollinear
    simp only [orient, PiLp.zero_apply, sub_zero, zr, wr, zero_mul, mul_zero]
  have upper : W.arg - Z.arg ≤ π := by linarith only [zb.1, wb.2]
  have modular := signedPlanarAngle_coe p q pn qn
  rw [← Real.Angle.coe_sub] at modular
  have lhs : ((signedPlanarAngle p q : Real.Angle).toReal) = signedPlanarAngle p q := by
    unfold signedPlanarAngle
    exact Complex.arg_coe_angle_toReal_eq_arg _
  have rhs : ((W.arg - Z.arg : ℝ) : Real.Angle).toReal = W.arg - Z.arg :=
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨lower, upper⟩
  change ((signedPlanarAngle p q : ℝ) : Real.Angle) =
    ((W.arg - Z.arg : ℝ) : Real.Angle) at modular
  exact lhs.symm.trans ((congrArg Real.Angle.toReal modular).trans rhs)

/-- When all rays lie in the same coordinate halfplane there is no full turn
inside a consistently oriented block, even if its boundary rays are vertical. -/
theorem sum_forward_ray_angles_le_pi {n : ℕ} (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i j : Fin (n + 1),
      0 < orient 0 (ray i.castSucc) (ray i.succ) * orient 0 (ray j.castSucc) (ray j.succ))
    (positive : ∀ i, 0 ≤ ray i 0) :
    (∑ i : Fin (n + 1), angle (ray i.castSucc) (ray i.succ)) ≤ π := by
  let θ (i : Fin (n + 2)) := (orientedComplex (ray i)).arg
  have angle_diff (i : Fin (n + 1)) :
      angle (ray i.castSucc) (ray i.succ) = |θ i.succ - θ i.castSucc| := by
    rw [← abs_signedPlanarAngle _ _ (genuine _) (genuine _),
      signedPlanarAngle_eq_arg_sub_of_halfplane (genuine _) (genuine _)
        (positive _) (positive _) (nonzero i)]
  have sign (i : Fin (n + 1)) :
      (0 ≤ θ i.succ - θ i.castSucc) ↔ 0 ≤ orient 0 (ray i.castSucc) (ray i.succ) := by
    rw [← signedPlanarAngle_eq_arg_sub_of_halfplane (genuine _) (genuine _)
      (positive _) (positive _) (nonzero i), signedPlanarAngle_nonneg_iff _ _ (genuine _)]
    simp only [orient, PiLp.zero_apply, sub_zero]
  have telescope :
      (∑ i : Fin (n + 1), (θ i.succ - θ i.castSucc)) = θ (Fin.last (n + 1)) - θ 0 := by
    rw [Finset.sum_sub_distrib]
    have one := Fin.sum_univ_succ θ
    have two := Fin.sum_univ_castSucc θ
    linarith only [one, two]
  have range (i : Fin (n + 2)) : θ i ∈ Set.Icc (-(π / 2)) (π / 2) := by
    have h : 0 ≤ (orientedComplex (ray i)).re := by rw [orientedComplex_re]; exact positive i
    exact ⟨Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl h), Complex.arg_le_pi_div_two_iff.mpr (Or.inl h)⟩
  let d (i : Fin (n + 1)) := orient 0 (ray i.castSucc) (ray i.succ)
  rcases lt_or_gt_of_ne (nonzero 0) with hn | hp
  · have order (i : Fin (n + 1)) : θ i.succ - θ i.castSucc ≤ 0 := by
      apply le_of_not_ge
      exact fun h => (not_le_of_gt (neg_of_mul_pos_left (consistent i 0) hn.le)) ((sign i).mp h)
    calc
      _ = -(∑ i : Fin (n + 1), (θ i.succ - θ i.castSucc)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => (angle_diff i).trans (abs_of_nonpos (order i)))
      _ ≤ _ := by rw [telescope]; linarith only [(range 0).2, (range (Fin.last (n + 1))).1]
  · have order (i : Fin (n + 1)) : 0 ≤ θ i.succ - θ i.castSucc :=
      (sign i).mpr (pos_of_mul_pos_left (consistent i 0) hp.le).le
    calc
      _ = ∑ i : Fin (n + 1), (θ i.succ - θ i.castSucc) :=
        Finset.sum_congr rfl (fun i _ => (angle_diff i).trans (abs_of_nonneg (order i)))
      _ ≤ _ := by rw [telescope]; linarith only [(range 0).1, (range (Fin.last (n + 1))).2]

end Unfoldings
