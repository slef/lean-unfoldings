module

public import Unfoldings.Geometry.HalfTurnRadialClosure
public import Unfoldings.Geometry.TrimmedEndpointAvoidance
public import Unfoldings.Geometry.SourceStartRadialTrim
public import Unfoldings.Geometry.RadialClosingLinks

/-! Every genuinely radial half-turn block admits a vertex-avoiding Jordan closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open InnerProductGeometry Real

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- First choose strict trimmed endpoints. The strict inequalities persist when
the trims, center and closing point are perturbed. -/
theorem exists_strict_halfturn_trim
    (radial : P.RadialFrom source 0) (nonzero : ∀ i, P.edge i ≠ 0)
    {γ : ℝ} (positive : 0 < γ)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < π)
    : ∃ (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane) (a b : unitInterval),
      (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      let Q := P.trimEnds a b
      source ∈ Q.strictRadialSources ∧
      0 < dist source (Q.vertex 0) ∧
      dist source (Q.vertex 0) < dist source (Q.vertex (Fin.last (n + 2))) ∧
      ∀ j, 0 < (frame.symm (Q.vertex j - source)).1 ∧
        0 < (frame.symm (Q.vertex j - source)).2 := by
  have ordered := P.vertex_radius_strictMono_of_radial source radial nonzero
  have genuine (i : Fin (n + 1)) : P.internalSourceRay source i ≠ 0 := by
    intro same
    have later := ordered (show (0 : Fin (n + 3)) < i.succ.castSucc by
      change 0 < i.val + 1
      omega)
    have equal : P.vertex i.succ.castSucc = source := sub_eq_zero.mp same
    change dist source (P.vertex 0) < dist source (P.vertex i.succ.castSucc) at later
    rw [equal, dist_self] at later
    exact (dist_nonneg : 0 ≤ dist source (P.vertex 0)).not_gt later
  obtain ⟨frame, a, b, first, last, inside⟩ :=
    P.exists_trimEnds_quadrant_of_halfturn source genuine small
  let Q := P.trimEnds a b
  have strict_initial : source ∈ Q.strictRadialSources ∧ 0 < dist source (Q.vertex 0) := by
    by_cases start : P.vertex 0 = source
    · exact P.strictRadialSource_trimEnds_start_at_source start radial nonzero positive margin
        a b first.1 first.2 last.1
    · have initial : 0 < dist source (P.vertex 0) := dist_pos.mpr (Ne.symm start)
      have strict : source ∈ P.strictRadialSources := by
        intro i edge
        have radius := initial.trans_le (ordered.monotone (Fin.zero_le i.castSucc))
        change 0 < dist source (P.vertex i.castSucc) at radius
        rw [dist_eq_norm'] at radius
        exact (mul_pos positive (mul_pos radius (norm_pos_iff.mpr edge))).trans_le (margin i)
      exact ⟨P.strictRadialSource_trimEnds strict a b first.2 last.1, initial.trans_le
        (P.path_radius_bounds source radial
          (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))).1⟩
  have progress := P.trimEnds_radius_progress a b radial (nonzero (Fin.last (n + 1))) last.1
  exact ⟨frame, a, b, first, last, strict_initial.1, strict_initial.2, progress, inside⟩

/-- Construct the generic closure for a strict polar window, even when its
initial point is the source. The trims and the entire three connector lines
avoid all listed old vertices. -/
theorem exists_regular_halfturn_closure {I A : Type*} [Finite I] [Finite A]
    (radial : P.RadialFrom source 0) (nonzero : ∀ i, P.edge i ≠ 0)
    {γ : ℝ} (positive : 0 < γ)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < π)
    (point : I → Plane) (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0)
    {δ : ℝ} (room : 0 < δ) :
    ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        let Q := P.trimEnds a b
        dist q source < δ ∧ Q.RadialFrom q 0 ∧
        0 < dist q (Q.vertex 0) ∧ dist q (Q.vertex 0) < dist q (Q.vertex (Fin.last (n + 2))) ∧
        (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q) (c - Q.vertex (Fin.last (n + 2))) ∧
        (∀ i, equation i q ≠ 0 ∧ equation i c ≠ 0) ∧
        (∀ i, Q.vertex 0 ≠ point i ∧ Q.vertex (Fin.last (n + 2)) ≠ point i) ∧
        (∀ (j : Fin 3) (t : ℝ) i,
          let link := radialClosingLinks q (Q.vertex 0) (Q.vertex (Fin.last (n + 2))) c j
          AffineMap.lineMap link.1 link.2 t ≠ point i) ∧
        Schoenflies.IsJordanCurve (Q.threeSegmentClosure q c) := by
  have ordered := P.vertex_radius_strictMono_of_radial source radial nonzero
  have genuine (i : Fin (n + 1)) : P.internalSourceRay source i ≠ 0 := by
    intro same
    have later := ordered (show (0 : Fin (n + 3)) < i.succ.castSucc by
      change 0 < i.val + 1
      omega)
    have equal : P.vertex i.succ.castSucc = source := sub_eq_zero.mp same
    change dist source (P.vertex 0) < dist source (P.vertex i.succ.castSucc) at later
    rw [equal, dist_self] at later
    exact (dist_nonneg : 0 ≤ dist source (P.vertex 0)).not_gt later
  obtain ⟨frame, a, b, first, last, first_avoids, last_avoids, inside⟩ :=
    P.exists_trimEnds_quadrant_of_halfturn_avoids source genuine small (nonzero 0)
      (nonzero (Fin.last (n + 1))) point
  let Q := P.trimEnds a b
  have strict_initial : source ∈ Q.strictRadialSources ∧ 0 < dist source (Q.vertex 0) := by
    by_cases start : P.vertex 0 = source
    · exact P.strictRadialSource_trimEnds_start_at_source start radial nonzero positive margin
        a b first.1 first.2 last.1
    · have initial : 0 < dist source (P.vertex 0) := dist_pos.mpr (Ne.symm start)
      have strict : source ∈ P.strictRadialSources := by
        intro i edge
        have radius := initial.trans_le (ordered.monotone (Fin.zero_le i.castSucc))
        change 0 < dist source (P.vertex i.castSucc) at radius
        rw [dist_eq_norm'] at radius
        exact (mul_pos positive (mul_pos radius (norm_pos_iff.mpr edge))).trans_le (margin i)
      exact ⟨P.strictRadialSource_trimEnds strict a b first.2 last.1, initial.trans_le
        (P.path_radius_bounds source radial
          (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))).1⟩
  have progress := P.trimEnds_radius_progress a b radial (nonzero (Fin.last (n + 1))) last.1
  have wedge (j : Fin (n + 3)) :
      0 ≤ (frame.symm (Q.vertex j - source)).1 ∧ 0 ≤ (frame.symm (Q.vertex j - source)).2 :=
    ⟨(inside j).1.le, (inside j).2.le⟩
  obtain ⟨q, c, height, close, radial', initial, advances, supported, outside, outward,
    regular, _, first_line, middle_line, last_line, jordan⟩ :=
    Q.exists_supported_line_avoiding_wedge_closure source strict_initial.1 strict_initial.2 progress
      frame wedge point equation proper room
  refine ⟨a, b, first, last, q, c, height, close, radial', initial, advances, supported, outside,
    outward, regular, fun i => ⟨first_avoids i, last_avoids i⟩, ?_, jordan⟩
  intro j t i
  fin_cases j
  · change AffineMap.lineMap (Q.vertex (Fin.last (n + 2))) c t ≠ point i
    intro equal
    exact last_avoids i (last_line i t equal).symm
  · change AffineMap.lineMap c q t ≠ point i
    rw [← AffineMap.lineMap_apply_one_sub]
    exact middle_line i (1 - t)
  · change AffineMap.lineMap q (Q.vertex 0) t ≠ point i
    rw [← AffineMap.lineMap_apply_one_sub]
    intro equal
    exact first_avoids i (first_line i (1 - t) equal).symm

end Unfoldings.PolygonalChain
