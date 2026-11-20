module

public import Unfoldings.FewestNets.CrossingChargeBound
public import Unfoldings.Geometry.SphericalArcEndpointClip

/-! The localized crossing charge uses the short portions at both endpoints. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation

/-- If every changed residual side admits a hit within a fixed reach of a network
endpoint, only twice that reach per network edge is charged in Crofton's formula. -/
theorem integral_componentCharge_le_of_endpoint_hits
    {E J : Type*} [Finite E] [DecidableEq E] [Fintype J]
    (s deleted : Finset E) (few : deleted.card ≤ 2)
    (changed : SpatialRotation → E → Prop) [∀ g, DecidablePred (changed g)]
    (u v : ↥(s \ deleted) → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    {reach : ℝ} (reach_nonneg : 0 ≤ reach)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (not_antipodal : ∀ i, u i + v i ≠ 0)
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ Real.pi / 2)
    (integrable : Integrable (fun g => componentCharge (s.filter (changed g)).card) probability)
    (not_one : ∀ᵐ g ∂probability, (s.filter (changed g)).card ≠ 1)
    (witness : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i : ↥(s \ deleted), changed g i.val →
        ∃ (j : J) (b : Bool) (x : Space), x ∈ openMinorArc (u i) (v i) ∧
          x ∈ linear g '' (linear (frame j) '' equatorialArc (radius j)) ∧
          angle (linear g (linear (frame j) (equatorPoint
            ((arcEndpointPhase (radius j) b : ℝ) : EquatorPhase)))) x ≤ reach) :
    (∫ g, componentCharge (s.filter (changed g)).card ∂probability) ≤
      (∑ i, angle (u i) (v i)) * (2 * Fintype.card J * reach) / (4 * Real.pi ^ 2) := by
  let clipFrame (j : J × Bool) := endpointClipFrame (frame j.1) (radius j.1) reach j.2
  let clipRadius (j : J × Bool) := endpointClipRadius (radius j.1) reach
  have clip_nonneg (j : J × Bool) : 0 ≤ clipRadius j :=
    endpointClipRadius_nonneg (nonneg j.1) reach_nonneg
  have clip_small (j : J × Bool) : clipRadius j ≤ Real.pi :=
    (min_le_left _ _).trans ((small j.1).trans (by linarith [Real.pi_pos]))
  have off_u : ∀ᵐ g ∂probability, ∀ (i : ↥(s \ deleted)) (j : J × Bool),
      inner ℝ (linear (g * clipFrame j) equatorPole) (u i) ≠ 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_not_on_moving_arc_circle (hu i) _
  have off_v : ∀ᵐ g ∂probability, ∀ (i : ↥(s \ deleted)) (j : J × Bool),
      inner ℝ (linear (g * clipFrame j) equatorPole) (v i) ≠ 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_not_on_moving_arc_circle (hv i) _
  have clipped_witness : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i : ↥(s \ deleted), changed g i.val →
        ∃ j, g ∈ arcCrossingEvent (u i) (v i) (clipFrame j) (clipRadius j) := by
    filter_upwards [witness, off_u, off_v] with g found u_off v_off
    intro many i changed_i
    obtain ⟨j, b, x, on_i, hit, close⟩ := found many i changed_i
    obtain ⟨y, on_j, rfl⟩ := hit
    have near : angle (linear (frame j) (equatorPoint
        ((arcEndpointPhase (radius j) b : ℝ) : EquatorPhase))) y ≤ reach := by
      change angle ((isometry g).toLinearIsometry _)
        ((isometry g).toLinearIsometry _) ≤ reach at close
      rw [(isometry g).toLinearIsometry.angle_map] at close
      exact close
    have on_clip := mem_endpointClip_of_angle_le (nonneg j) (small j) reach_nonneg on_j near
    exact ⟨(j, b), mem_arcCrossingEvent_of_hit (hu i) (hv i) (not_antipodal i)
      (u_off i (j, b)) (v_off i (j, b)) on_i ⟨y, on_clip, rfl⟩⟩
  have estimate := integral_componentCharge_le_of_crossing_witnesses s deleted few changed
    u v clipFrame clipRadius hu hv not_antipodal clip_nonneg clip_small integrable not_one
    clipped_witness
  have sum_clips : (∑ j, 2 * clipRadius j) ≤ 2 * Fintype.card J * reach := calc
    _ ≤ ∑ _ : J × Bool, reach :=
      Finset.sum_le_sum fun j _ => two_mul_endpointClipRadius_le (radius j.1) reach
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  exact estimate.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sum_clips
    (Finset.sum_nonneg fun i _ => angle_nonneg (u i) (v i))) (by positivity))

end Unfoldings.FewestNets
