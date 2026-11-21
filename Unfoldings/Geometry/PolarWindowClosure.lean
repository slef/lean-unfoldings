module

public import Unfoldings.Geometry.GenericWedgeClosure
public import Unfoldings.Cone.Sector
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Generic radial-wedge closures in every strict half-turn window. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

/-- Two rays separated by less than half a turn give linear coordinates
in which every direction of their closed angular sector is nonnegative. -/
theorem exists_polarWindow_frame (R : ℂ ≃ₗᵢ[ℝ] Plane) {a b : ℝ}
    (positive : 0 < b - a) (small : b - a < π) :
    ∃ frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane,
      ∀ θ ∈ Set.Icc a b, 0 ≤ (frame.symm (R (polarRay θ))).1 ∧
        0 ≤ (frame.symm (R (polarRay θ))).2 := by
  let u := R (polarRay a)
  let v := R (polarRay b)
  have un : u ≠ 0 := by
    simpa only [u, map_zero] using R.injective.ne (polarRay_ne_zero a)
  have vn : v ≠ 0 := by
    simpa only [v, map_zero] using R.injective.ne (polarRay_ne_zero b)
  have θ : angle u v = b - a := (R.toLinearIsometry.angle_map _ _).trans
    (angle_polarRay a b positive.le small.le)
  have indep : LinearIndependent ℝ ![u, v] := by
    apply (LinearIndependent.pair_iff' un).mpr
    intro s eq
    rcases lt_trichotomy s 0 with neg | zero | pos
    · rw [← eq, angle_smul_right_of_neg _ _ neg, angle_neg_right, angle_self un, sub_zero] at θ
      exact small.ne' θ
    · exact vn (by simpa only [zero, zero_smul] using eq.symm)
    · rw [← eq, angle_smul_right_of_pos _ _ pos, angle_self un] at θ
      exact positive.ne' θ.symm
  let B := basisOfLinearIndependentOfCardEqFinrank indep (by simp [Plane])
  let frame := (LinearEquiv.finTwoArrow ℝ ℝ).symm.trans B.equivFun.symm
  have value (s t : ℝ) : frame (s, t) = s • u + t • v := by
    have pair : (LinearEquiv.finTwoArrow ℝ ℝ).symm (s, t) = ![s, t] := by
      funext i
      fin_cases i <;> rfl
    change B.equivFun.symm ((LinearEquiv.finTwoArrow ℝ ℝ).symm (s, t)) = _
    rw [pair, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp [B]
  refine ⟨frame, fun c hc => ?_⟩
  obtain ⟨s, spos, t, tpos, combo⟩ := polarRay_mem_positive_span a b c positive small hc
  have h := congrArg R combo
  simp only [map_add, map_smul] at h
  change R (polarRay c) = s • u + t • v at h
  rw [h, ← value, frame.symm_apply_apply]
  exact ⟨spos, tpos⟩

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (source : Plane)

/-- A strict half-turn window supplies the linear wedge needed for generic
Jordan closure, including after a small perturbation of the radial source. -/
theorem exists_generic_radial_closure_of_polarWindow {ι κ : Type*} [Finite ι] [Finite κ]
    (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (R : ℂ ≃ₗᵢ[ℝ] Plane) {a b : ℝ} (positive : 0 < b - a) (small : b - a < π)
    (headings : ∀ j, ∃ (r : ℝ) (θ : ℝ), 0 ≤ r ∧ θ ∈ Set.Icc a b ∧
      P.vertex j - source = r • R (polarRay θ))
    (sourceEq : ι → Plane →ᵃ[ℝ] ℝ) (sourceProper : ∀ j, sourceEq j ≠ 0)
    (closingEq : Plane → κ → Plane →ᵃ[ℝ] ℝ)
    (closingProper : ∀ q, (∀ j, sourceEq j q ≠ 0) → ∀ j, closingEq q j ≠ 0)
    {δ : ℝ} (radius : 0 < δ) :
    ∃ q c : Plane, dist q source < δ ∧ (∀ j, sourceEq j q ≠ 0) ∧
      (∀ j, closingEq q j c ≠ 0) ∧ P.RadialFrom q 0 ∧
      Schoenflies.IsJordanCurve (Set.range P.path ∪
        ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c q) ∪
          segment ℝ q (P.vertex 0))) := by
  obtain ⟨frame, sectors⟩ := exists_polarWindow_frame R positive small
  have vertex_inside (j : Fin (n + 1)) : 0 ≤ (frame.symm (P.vertex j - source)).1 ∧
      0 ≤ (frame.symm (P.vertex j - source)).2 := by
    obtain ⟨r, t, hr, ht, eq⟩ := headings j
    rw [eq, map_smul]
    exact ⟨mul_nonneg hr (sectors t ht).1, mul_nonneg hr (sectors t ht).2⟩
  obtain ⟨q, close, radial, init, inc, vertices, good_source⟩ :=
    P.exists_generic_radial_source source strict initial progress frame vertex_inside sourceEq
      sourceProper radius
  let left := (LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap
  let right := (LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap
  have path_inside (z : Plane) (member : z ∈ Set.range P.path) :
      0 ≤ (frame.symm (z - q)).1 ∧ 0 ≤ (frame.symm (z - q)).2 :=
    ⟨P.height_nonneg_on_path q left (fun j => (vertices j).1.le) member,
      P.height_nonneg_on_path q right (fun j => (vertices j).2.le) member⟩
  obtain ⟨c, good_close, _, _, jordan⟩ := P.exists_generic_radial_wedge_closure q radial init inc
    frame path_inside (closingEq q) (closingProper q good_source)
  exact ⟨q, c, close, good_source, good_close, radial, jordan⟩

end PolygonalChain
end Unfoldings
