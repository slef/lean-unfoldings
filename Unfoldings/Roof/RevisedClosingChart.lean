module

public import Unfoldings.Roof.ShortClosingBend
public import Unfoldings.Roof.HorizontalReorientation
public import Unfoldings.Geometry.DirectionFrame
public import Unfoldings.Geometry.ReorientedChain

/-! The regular two-link closure in a chart aligned with its physical long link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem sectionDirection_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) (d : Plane) :
    (K.reorient E).sectionDirection f (E d) = horizontalChartIsometry E (K.sectionDirection f d) := by
  rw [sectionDirection, sectionDirection, K.normalSlope_reorient, E.inner_map_map,
    horizontalChartIsometry_apply, horizontal_horizontalAtHeight]
  rfl

open Classical in
set_option maxHeartbeats 1500000 in
/-- Rotating the whole construction preserves the actual bend error, and the
new chart has strictly increasing bank edges and a horizontal long link. -/
theorem exists_regular_horizontal_shortClosing {n : ℕ} (P : PolygonalChain Plane n)
    (n_pos : 0 < n) (acute : ∀ i, 0 < inner ℝ (P.vertex (Fin.last n) - P.vertex 0) (P.edge i))
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, P.vertex 0 ≠ point i)
    (last : ∀ i, P.vertex (Fin.last n) ≠ point i) {D : Set Plane}
    (opened : IsOpen D) (a_in : P.vertex 0 ∈ D) (b_in : P.vertex (Fin.last n) ∈ D)
    {r η : ℝ} (rp : 0 < r) (ηp : 0 < η) :
    ∃ (E : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane),
      let Q := P.reorient E
      let a := Q.vertex 0
      let b := Q.vertex (Fin.last n)
      c ∈ E '' D ∧ c ∈ Metric.ball b r ∧
      (∀ i, 0 < Q.edge i 0) ∧ a 0 < c 0 ∧ c 0 < b 0 ∧ c 1 = a 1 ∧
      (∀ j, edge j (E.symm c) ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (Q.twoClosingLinks c j).1 (Q.twoClosingLinks c j).2 t ≠ E (point i)) ∧
      (Set.range Q.path ∩ Set.range (Q.forwardClosingChain c).path).Finite ∧
      (∀ p ∈ Set.range Q.path, c 0 ≤ p 0 → p ∈ Metric.ball b r) ∧
      angle (c - a) (b - c) < η ∧
      ∀ f, |angle ((K.reorient E).sectionDirection f (c - a)) ((K.reorient E).sectionDirection f (b - c)) -
        angle (c - a) (b - c)| < η := by
  obtain ⟨d, hd, progress, right, generic, no_vertex, finite, tail, turn, error⟩ :=
    K.exists_regular_shortClosing_bend P n_pos acute point edge proper first last opened a_in b_in rp ηp
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let v := d - a
  let E := directionFrame v
  let Q := P.reorient E
  have nv : v ≠ 0 := by
    intro zero
    change 0 < inner ℝ v (b - d) at right
    simpa [zero] using right
  have norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr nv
  have coord (x : Plane) : ‖v‖ * E x 0 = inner ℝ v x := directionFrame_coord v x
  have x_forward (i : Fin n) : 0 < Q.edge i 0 := by
    rw [show Q.edge i = E (P.edge i) from P.reorient_edge E i]
    have h := progress i
    change 0 < inner ℝ v (P.edge i) at h
    rw [← coord] at h
    exact pos_of_mul_pos_right h norm_pos.le
  have first_x : Q.vertex 0 0 < E d 0 := by
    change E a 0 < E d 0
    have h : E v 0 = ‖v‖ := directionFrame_horizontal v
    rw [show E v = E d - E a from map_sub E d a] at h
    change E d 0 - E a 0 = ‖v‖ at h
    linarith only [h, norm_pos]
  have last_x : E d 0 < Q.vertex (Fin.last n) 0 := by
    have h : 0 < ‖v‖ * E (b - d) 0 := (coord (b - d)).symm ▸ right
    have h := pos_of_mul_pos_right h norm_pos.le
    rw [map_sub] at h
    exact sub_pos.mp h
  have horiz : E d 1 = Q.vertex 0 1 := by
    have h : E v 1 = 0 := directionFrame_vertical v
    rw [show E v = E d - E a from map_sub E d a] at h
    exact sub_eq_zero.mp h
  have ball (x : Plane) (hx : x ∈ Metric.ball b r) : E x ∈ Metric.ball (E b) r := by
    simpa only [Metric.mem_ball, E.dist_map] using hx
  have planar_angle (u w : Plane) : angle (E u) (E w) = angle u w :=
    E.toLinearIsometry.angle_map u w
  have spatial_angle (u w : Space) :
      angle (horizontalChartIsometry E u) (horizontalChartIsometry E w) = angle u w :=
    (horizontalChartIsometry E).toLinearIsometry.angle_map u w
  refine ⟨E, E d, Set.mem_image_of_mem E hd.1, ball d hd.2, x_forward, first_x, last_x,
    horiz, fun j => by rw [E.symm_apply_apply]; exact generic j, ?_, ?_, ?_, ?_, ?_⟩
  · intro j t i equal
    apply no_vertex j t i
    apply E.injective
    fin_cases j
    · exact ((PolygonalChain.lineMap_reorient E _ _ t).symm.trans equal)
    · exact ((PolygonalChain.lineMap_reorient E _ _ t).symm.trans equal)
  · rw [P.path_range_reorient E, P.forwardClosingChain_reorient E d,
      (P.forwardClosingChain d).path_range_reorient E, ← Set.image_inter E.injective]
    exact finite.image E
  · intro x on x_after
    obtain ⟨y, on_y, rfl⟩ := (P.path_range_reorient E).subset on
    apply ball y
    apply tail y on_y
    rw [← coord d, ← coord y]
    exact mul_le_mul_of_nonneg_left x_after norm_pos.le
  · change angle (E d - E a) (E b - E d) < η
    rw [← map_sub, ← map_sub, planar_angle]
    exact turn
  · intro f
    change |angle ((K.reorient E).sectionDirection f (E d - E a))
      ((K.reorient E).sectionDirection f (E b - E d)) - angle (E d - E a) (E b - E d)| < η
    rw [← map_sub, ← map_sub, K.sectionDirection_reorient, K.sectionDirection_reorient,
      spatial_angle, planar_angle]
    exact error f

end Unfoldings.ConvexRoof
