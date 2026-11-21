module

public import Unfoldings.Geometry.ShortPolarWindow
public import Unfoldings.Geometry.RayWindowTrimming

/-! Linear quadrant coordinates for radial windows of variation below π. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

/-- A positive rescaling and an invertible sum-and-difference change of coordinates. -/
private def widenQuadrant (m : ℝ) (nonzero : m ≠ 0) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 + p.2 / m, p.1 - p.2 / m)
  invFun q := ((q.1 + q.2) / 2, m * (q.1 - q.2) / 2)
  left_inv p := by
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring
  right_inv q := by
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring
  map_add' p q := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, add_div] <;> ring
  map_smul' c p := by
    apply Prod.ext
    · change c * p.1 + (c * p.2) / m = c * (p.1 + p.2 / m)
      ring
    · change c * p.1 - (c * p.2) / m = c * (p.1 - p.2 / m)
      ring

/-- Every finite set of genuinely acute rays fits in a pointed linear quadrant. -/
theorem exists_quadrantFrame_of_acute_axis {I : Type*} [Finite I] [Nonempty I]
    (ray : I → Plane) (axis : Plane) (axis_ne : axis ≠ 0)
    (acute : ∀ i, angle axis (ray i) < π / 2) :
    ∃ frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane, ∀ i,
      0 < (frame.symm (ray i)).1 ∧ 0 < (frame.symm (ray i)).2 := by
  classical
  let := Fintype.ofFinite I
  let L : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let z := L axis
  have nonzero : z ≠ 0 := by simpa only [z, map_zero] using L.injective.ne axis_ne
  let unit := Units.mk0 z⁻¹ (inv_ne_zero nonzero)
  let E := (L.toLinearEquiv.trans (unit.mulLeftLinearEquiv ℝ ℂ)).trans
    Complex.equivRealProdCLM.toLinearEquiv
  have positive (i : I) : 0 < (E (ray i)).1 := by
    have ip : 0 < inner ℝ z (L (ray i)) := by
      rw [L.inner_map_map]
      by_contra! outside
      exact (acute i).not_ge (inner_nonpos_iff_pi_div_two_le_angle.mp outside)
    have re : 0 < (L (ray i) / z).re := by
      have eq : (L (ray i) / z).re = inner ℝ z (L (ray i)) / Complex.normSq z := by
        rw [Complex.div_re, ← add_div, Complex.inner, Complex.mul_re,
          Complex.conj_re, Complex.conj_im]
        ring
      rw [eq]
      exact div_pos ip (Complex.normSq_pos.mpr nonzero)
    change 0 < (z⁻¹ * L (ray i)).re
    simpa only [div_eq_inv_mul] using re
  let ratio (i : I) : ℝ := |(E (ray i)).2| / (E (ray i)).1
  obtain ⟨j, _, largest⟩ := Finset.exists_max_image (Finset.univ : Finset I) ratio
    Finset.univ_nonempty
  let m := ratio j + 1
  have m_pos : 0 < m := by
    have r_nonnegative : 0 ≤ ratio j := div_nonneg (abs_nonneg _) (positive j).le
    dsimp only [m]
    linarith
  let frame := (E.trans (widenQuadrant m m_pos.ne')).symm
  refine ⟨frame, fun i => ?_⟩
  let x := E (ray i)
  have small : |x.2| / m < x.1 := by
    have h : ratio i < m := (largest i (Finset.mem_univ i)).trans_lt (by dsimp [m]; linarith)
    have bound := (div_lt_iff₀ (positive i)).mp h
    exact (div_lt_iff₀ m_pos).mpr (by simpa only [mul_comm] using bound)
  rw [← abs_of_pos m_pos, ← abs_div] at small
  have signs := abs_lt.mp small
  change 0 < x.1 + x.2 / m ∧ 0 < x.1 - x.2 / m
  constructor <;> linarith only [signs.1, signs.2]

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- Strict half-turn variation suffices to place the trimmed bank in a
pointed wedge, with both trimmed ends still on their original links. -/
theorem exists_trimEnds_quadrant_of_halfturn
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0)
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < π) :
    ∃ (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane) (a b : unitInterval),
      (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∀ j, 0 < (frame.symm ((P.trimEnds a b).vertex j - source)).1 ∧
        0 < (frame.symm ((P.trimEnds a b).vertex j - source)).2 := by
  obtain ⟨axis, nonzero, acute⟩ :=
    exists_acute_axis_of_short_polar_window (P.internalSourceRay source) genuine small
  obtain ⟨frame, positive⟩ :=
    exists_quadrantFrame_of_acute_axis (P.internalSourceRay source) axis nonzero acute
  let U : Set Plane := {z | 0 < (frame.symm (z - source)).1 ∧
    0 < (frame.symm (z - source)).2}
  have continuous : Continuous frame.symm := frame.symm.continuous_of_finiteDimensional
  have opened : IsOpen U :=
    (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).fst)).inter
      (isOpen_lt continuous_const ((continuous.comp (continuous_id.sub continuous_const)).snd))
  have internal (j : Fin (n + 3)) (first : 0 < j.val) (last : j.val < n + 2) : P.vertex j ∈ U := by
    let i : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have same : P.internalSourceRay source i = P.vertex j - source := by
      apply congrArg (fun k => P.vertex k - source)
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    have bound := positive i
    rw [same] at bound
    exact bound
  obtain ⟨a, b, first, last, inside⟩ := P.exists_trimEnds_vertices_mem opened internal
  exact ⟨frame, a, b, first, last, inside⟩

end PolygonalChain
end Unfoldings
