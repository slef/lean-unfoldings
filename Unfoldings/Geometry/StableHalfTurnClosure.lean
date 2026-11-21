module

public import Unfoldings.Geometry.RegularHalfTurnClosure

/-! A compact region can be chosen before listing the vertices of the completion mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open InnerProductGeometry Real

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- Replace the two endpoints while testing strict geometric conditions in the ambient plane. -/
private def endVertex (x y : Plane) (j : Fin (n + 3)) : Plane :=
  if j.val = 0 then x else if j.val = n + 2 then y else P.vertex j

private theorem endVertex_trim (a b : unitInterval) (j : Fin (n + 3)) :
    endVertex P (P.point 0 a) (P.point (Fin.last (n + 1)) b) j = (P.trimEnds a b).vertex j := rfl

/-- The two trimmed ends, the center and the corner lie in separate open sets
on whose product all strict closure tests hold. These sets are fixed before
any old vertices or edges have to be avoided. -/
theorem exists_stable_halfturn_closure
    (radial : P.RadialFrom source 0) (nonzero : ∀ i, P.edge i ≠ 0)
    {γ : ℝ} (positive : 0 < γ)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < π) :
    ∃ (U V W T : Set Plane) (a b : unitInterval) (c : Plane) (height : Plane →ₗ[ℝ] ℝ),
      IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ IsOpen T ∧
      P.point 0 a ∈ U ∧ P.point (Fin.last (n + 1)) b ∈ V ∧ source ∈ W ∧ c ∈ T ∧
      ∀ (a' b' : unitInterval) (q c' : Plane),
        P.point 0 a' ∈ U → P.point (Fin.last (n + 1)) b' ∈ V → q ∈ W → c' ∈ T →
        let Q := P.trimEnds a' b'
        Q.RadialFrom q 0 ∧ 0 < dist q (Q.vertex 0) ∧
        dist q (Q.vertex 0) < dist q (Q.vertex (Fin.last (n + 2))) ∧
        (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c' - q) < 0 ∧
        0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q) (c' - Q.vertex (Fin.last (n + 2))) := by
  obtain ⟨frame, a, b, first, last, strict, initial, progress, wedge⟩ :=
    P.exists_strict_halfturn_trim source radial nonzero positive margin small
  let Q := P.trimEnds a b
  let x := P.point 0 a
  let y := P.point (Fin.last (n + 1)) b
  have trim_genuine (i : Fin (n + 2)) : Q.edge i ≠ 0 := by
    rw [P.trimEnds_edge]
    apply smul_ne_zero _ (nonzero i)
    split_ifs <;> linarith [first.2, last.1]
  let fst := (LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap
  let snd := (LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap
  have coords (z : Plane) (member : z ∈ Set.range Q.path) :
      0 ≤ (frame.symm (z - source)).1 ∧ 0 ≤ (frame.symm (z - source)).2 :=
    ⟨Q.height_nonneg_on_path source fst (fun j => (wedge j).1.le) member,
      Q.height_nonneg_on_path source snd (fun j => (wedge j).2.le) member⟩
  obtain ⟨c, outside, outward, _⟩ := Q.exists_radial_wedge_closure source
    (Q.radialFrom_of_strictRadialSource strict) initial progress frame coords
  obtain ⟨height, supported, excluded⟩ : ∃ height : Plane →ₗ[ℝ] ℝ,
      (∀ j, 0 < height (Q.vertex j - source)) ∧ height (c - source) < 0 := by
    rcases outside with left | right
    · exact ⟨fst, fun j => (wedge j).1, left⟩
    · exact ⟨snd, fun j => (wedge j).2, right⟩
  let Z := Plane × (Plane × (Plane × Plane))
  let X (z : Z) := z.1
  let Y (z : Z) := z.2.1
  let q (z : Z) := z.2.2.1
  let d (z : Z) := z.2.2.2
  let v (j : Fin (n + 3)) (z : Z) := endVertex P (X z) (Y z) j
  have continuous_x : Continuous X := continuous_fst
  have continuous_y : Continuous Y := continuous_fst.comp continuous_snd
  have continuous_q : Continuous q := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have continuous_d : Continuous d := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have continuous_v (j : Fin (n + 3)) : Continuous (v j) := by
    dsimp only [v, endVertex]
    split_ifs <;> fun_prop
  have continuous_h : Continuous height := height.continuous_of_finiteDimensional
  let R : Set Z :=
    {z | 0 < dist (q z) (X z) ∧ dist (q z) (X z) < dist (q z) (Y z) ∧
      height (d z - q z) < 0 ∧ 0 < inner ℝ (Y z - q z) (d z - Y z)} ∩
    (⋂ j, {z | 0 < height (v j z - q z)}) ∩
    ⋂ i : Fin (n + 2), {z | 0 < inner ℝ (v i.castSucc z - q z) (v i.succ z - v i.castSucc z)}
  have continuous_outward : Continuous (fun z : Z => inner ℝ (Y z - q z) (d z - Y z)) := by
    fun_prop
  have open_R : IsOpen R := by
    apply IsOpen.inter
    · apply IsOpen.inter
      · exact (isOpen_lt continuous_const (continuous_q.dist continuous_x)).inter
          ((isOpen_lt (continuous_q.dist continuous_x) (continuous_q.dist continuous_y)).inter
            ((isOpen_lt (continuous_h.comp (continuous_d.sub continuous_q)) continuous_const).inter
              (isOpen_lt continuous_const continuous_outward)))
      · exact isOpen_iInter_of_finite (fun j =>
          isOpen_lt continuous_const (continuous_h.comp ((continuous_v j).sub continuous_q)))
    · exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (by fun_prop))
  have anchor : (x, y, source, c) ∈ R := by
    refine ⟨⟨⟨?_, ?_, excluded, ?_⟩, Set.mem_iInter.mpr (fun j => ?_)⟩,
      Set.mem_iInter.mpr (fun i => ?_)⟩
    · simpa only [Q, P.trimEnds_start] using initial
    · simpa only [Q, P.trimEnds_start, P.trimEnds_last] using progress
    · simpa only [Q, P.trimEnds_last] using outward
    · exact supported j
    · exact strict i (trim_genuine i)
  obtain ⟨U, V₀, hU, hV₀, hx, hv₀, sub₀⟩ := isOpen_prod_iff.mp open_R _ _ anchor
  obtain ⟨V, W₀, hV, hW₀, hy, hw₀, sub₁⟩ := isOpen_prod_iff.mp hV₀ _ _ hv₀
  obtain ⟨W, T, hW, hT, hq, hc, sub₂⟩ := isOpen_prod_iff.mp hW₀ _ _ hw₀
  refine ⟨U, V, W, T, a, b, c, height, hU, hV, hW, hT, hx, hy, hq, hc,
    fun a' b' q' c' hfirst hlast hq' hc' => ?_⟩
  let Q' := P.trimEnds a' b'
  let z : Z := (P.point 0 a', P.point (Fin.last (n + 1)) b', q', c')
  have belongs : z ∈ R := sub₀ ⟨hfirst, sub₁ ⟨hlast, sub₂ ⟨hq', hc'⟩⟩⟩
  obtain ⟨⟨⟨initial', progress', excluded', outward'⟩, supported'⟩, strict'⟩ := belongs
  have strict_q : q' ∈ Q'.strictRadialSources := fun i _ => Set.mem_iInter.mp strict' i
  refine ⟨Q'.radialFrom_of_strictRadialSource strict_q, ?_, ?_, ?_, excluded', ?_⟩
  · simpa only [P.trimEnds_start] using initial'
  · simpa only [P.trimEnds_start, P.trimEnds_last] using progress'
  · intro w hw
    exact Q'.height_nonneg_on_path q' height
      (fun j => (show 0 < height (Q'.vertex j - q') from Set.mem_iInter.mp supported' j).le) hw
  · simpa only [P.trimEnds_last] using outward'

end Unfoldings.PolygonalChain
