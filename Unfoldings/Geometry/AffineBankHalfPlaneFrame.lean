module

public import Unfoldings.Geometry.DirectedEdgeHalfPlaneFrame
public import Unfoldings.Geometry.TriangleWithEdge

/-! Directed coordinates for any genuine affine half-plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MetricGluing

/-- A nonzero affine side test with a prescribed directed boundary admits a rigid half-plane
frame centered at the first endpoint and preserving forward arclength. -/
theorem exists_affineBankHalfPlaneFrame (p q : Plane) (different : p ≠ q)
    (h : Plane →ᵃ[ℝ] ℝ) (proper : h ≠ 0) (pzero : h p = 0) (qzero : h q = 0)
    (occupied : Bool) :
    ∃ F : Plane ≃ᵃⁱ[ℝ] ℂ,
      (∀ s : ℝ, F (AffineMap.lineMap p q s) = ((s * ‖q - p‖ : ℝ) : ℂ)) ∧
      ∀ x, F x ∈ bankHalfPlane occupied ↔ 0 ≤ h x := by
  let T := triangleWithEdge p q different
  let c := h (T.opposite 0)
  have value (x : Plane) : h x = c * T.coord (Triangle.next (Triangle.next 0)) x :=
    T.affine_height_eq_coord 0 h pzero qzero x
  have nonzero : c ≠ 0 := by
    intro hz
    apply proper
    ext x
    rw [value, hz, zero_mul]
    rfl
  let reverse := decide (c < 0)
  obtain ⟨F, param, half⟩ := T.exists_directedEdgeHalfPlaneFrame 0 false false 0
  have line (s : ℝ) : F (AffineMap.lineMap p q s) = ((s * ‖q - p‖ : ℝ) : ℂ) := by
    have time := param s
    change F (AffineMap.lineMap p q s) = (((s - 0) * ‖q - p‖ : ℝ) : ℂ) at time
    rwa [sub_zero] at time
  let A := F.trans (bankAxisFrame false (xor occupied reverse)).toAffineIsometryEquiv
  refine ⟨A, ?_, ?_⟩
  · intro s
    change bankAxisFrame false (xor occupied reverse) (F (AffineMap.lineMap p q s)) = _
    rw [line s]
    exact bankAxisFrame_ofReal false _ _
  · intro x
    have original : 0 ≤ (F x).im ↔ 0 ≤ T.coord (Triangle.next (Triangle.next 0)) x := half x
    let k := Complex.imCLM.toLinearMap.toAffineMap.comp F.toAffineEquiv.toAffineMap
    have pe : k p = 0 := by
      change (F p).im = 0
      have u := congrArg Complex.im (line 0)
      simpa only [AffineMap.lineMap_apply_zero, Complex.ofReal_im] using u
    have qe : k q = 0 := by
      change (F q).im = 0
      have u := congrArg Complex.im (line 1)
      simpa only [AffineMap.lineMap_apply_one, Complex.ofReal_im] using u
    have altitude (z : Plane) : (F z).im =
        k (T.opposite 0) * T.coord (Triangle.next (Triangle.next 0)) z :=
      T.affine_height_eq_coord 0 k pe qe z
    have altitude_ne : k (T.opposite 0) ≠ 0 := by
      intro hz
      have hI := altitude (F.symm Complex.I)
      rw [hz, zero_mul, F.apply_symm_apply, Complex.I_im] at hI
      exact one_ne_zero hI
    have reversed : (F x).im ≤ 0 ↔ T.coord (Triangle.next (Triangle.next 0)) x ≤ 0 := by
      have zero : (F x).im = 0 ↔ T.coord (Triangle.next (Triangle.next 0)) x = 0 := by
        rw [altitude, mul_eq_zero, or_iff_right altitude_ne]
      constructor
      · intro h
        by_contra he
        have hi := original.mpr (lt_of_not_ge he).le
        exact (ne_of_gt (lt_of_not_ge he)) (zero.mp (le_antisymm h hi))
      · intro h
        by_contra he
        have hi := original.mp (lt_of_not_ge he).le
        exact (ne_of_gt (lt_of_not_ge he)) (zero.mpr (le_antisymm h hi))
    change bankAxisFrame false (xor occupied reverse) (F x) ∈ bankHalfPlane occupied ↔ 0 ≤ h x
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · have product : 0 ≤ c * T.coord (Triangle.next (Triangle.next 0)) x ↔
          T.coord (Triangle.next (Triangle.next 0)) x ≤ 0 := by
        constructor
        · intro hx
          by_contra hn
          exact (not_lt_of_ge hx) (mul_neg_of_neg_of_pos neg (lt_of_not_ge hn))
        · exact mul_nonneg_of_nonpos_of_nonpos neg.le
      cases occupied <;>
        simp [reverse, neg, bankHalfPlane, bankAxisFrame_im, value, product, reversed]
    · have sign : ¬ c < 0 := not_lt_of_gt pos
      cases occupied <;>
        simp [reverse, sign, bankHalfPlane, bankAxisFrame_im, value, pos, original]

end Unfoldings
