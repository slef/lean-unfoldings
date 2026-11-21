module

public import Unfoldings.FewestNets.VoronoiNetwork
public import Unfoldings.FewestNets.LocalizedCharge
public import Unfoldings.FewestNets.ComponentCountBudget

/-! Apply the local and global Crofton estimates with a common residual side set. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory InnerProductGeometry SpatialRotation Real
open scoped BigOperators

/-- The total geodesic length of the indexed network edges. -/
def networkLength {J : Type*} [Fintype J] (endpoint : J → Bool → Space) : ℝ :=
  ∑ j, angle (endpoint j false) (endpoint j true)

theorem networkLength_nonneg {J : Type*} [Fintype J] (endpoint : J → Bool → Space) :
    0 ≤ networkLength endpoint :=
  Finset.sum_nonneg (fun _ _ => angle_nonneg _ _)

/-- The small- and large-diameter Crofton estimates give the area-weighted
charge bound for the same choice of omitted sides. -/
theorem expected_charge_of_voronoi_network
    {I J E W : Type*} [Fintype J] [Finite E] [DecidableEq E] [Finite W]
    {site : I → Space} {endpoint : J → Bool → Space} {separation psi : ℝ}
    (H : VoronoiNetwork site endpoint separation psi)
    (s deleted : Finset E) (few : deleted.card ≤ 2)
    (changed : SpatialRotation → E → Prop) [∀ g, DecidablePred (changed g)]
    (u v : E → Space) (hu : ∀ i ∈ s, ‖u i‖ = 1) (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (not_antipodal : ∀ i ∈ s, u i + v i ≠ 0)
    (f : W → Space →L[ℝ] ℝ) (f_ne : ∀ i, f i ≠ 0)
    (boundary : ∀ i ∈ s, ∀ x ∈ openMinorArc (u i) (v i),
      (∀ k, 0 ≤ f k x) ∧ ∃ k, f k x = 0)
    (apart : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (openMinorArc (u i) (v i)) (openMinorArc (u j) (v j)))
    {d A t : ℝ} (diameter_nonneg : 0 ≤ d) (area_nonneg : 0 ≤ A) (sin_pos : 0 < t)
    (diameter : ∀ x, ‖x‖ = 1 → (∀ k, 0 ≤ f k x) →
      ∀ y, ‖y‖ = 1 → (∀ k, 0 ≤ f k y) → angle x y ≤ d)
    (small_sides : d ≤ 1 → (∑ i : ↥(s \ deleted), angle (u i.val) (v i.val)) * d ≤
      4 / (cos (d / 2) ^ 2 * t) * A)
    (large_sides : (∑ i : ↥(s \ deleted), angle (u i.val) (v i.val)) * d ≤ 8 / t * A)
    (integrable : Integrable (fun g => componentCharge (s.filter (changed g)).card) probability)
    (not_one : ∀ᵐ g ∂probability, (s.filter (changed g)).card ≠ 1)
    (hits : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i ∈ s, changed g i → ∃ j x, x ∈ openMinorArc (u i) (v i) ∧
        x ∈ openMinorArc (linear g (endpoint j false)) (linear g (endpoint j true))) :
    (∫ g, componentCharge (s.filter (changed g)).card ∂probability) ≤
      (componentCoefficient (Fintype.card J) (networkLength endpoint) separation psi / t) *
        (A / (4 * π)) := by
  let S := ∑ i : ↥(s \ deleted), angle (u i.val) (v i.val)
  let length (j : J) := angle (endpoint j false) (endpoint j true)
  let radius (j : J) := length j / 2
  have short (j : J) : length j < π := (H.edgeShort j).trans_lt (by linarith [pi_pos])
  have sin_psi : 0 < sin (psi / 2) := sin_pos_of_pos_of_lt_pi (by linarith [H.incidentPositive])
    (by linarith [H.incidentSmall, pi_pos])
  apply expectedCharge_le_area (Nat.cast_nonneg _) (networkLength_nonneg endpoint)
    H.separationPositive H.separationSmall sin_psi sin_pos diameter_nonneg area_nonneg
    (S := S) small_sides large_sides
  · intro small
    have local_bound := integral_componentCharge_le_of_small_diameter s deleted few changed
      u v hu hv not_antipodal f f_ne boundary apart diameter_nonneg small H.incidentPositive
      H.incidentSmall diameter endpoint H.edgeUnit H.edgePositive H.edgeShort H.separated H.incident
      integrable not_one hits
    apply local_bound.trans
    apply le_of_eq
    change (Fintype.card J : ℝ) * (S * d) / (4 * π * sin (psi / 2)) = _
    field_simp [pi_ne_zero, sin_psi.ne']
  · intro _
    choose frame carrier ends using fun j =>
      exists_frame_closedMinorArc_with_endpoints (H.edgeUnit j false) (H.edgeUnit j true)
        (H.edgePositive j) (short j)
    have radius_nonneg (j : J) : 0 ≤ radius j := div_nonneg (H.edgePositive j).le (by norm_num)
    have radius_small (j : J) : radius j ≤ π := by
      change length j / 2 ≤ _
      linarith [short j, pi_pos]
    have keep (i : ↥(s \ deleted)) : i.val ∈ s := (Finset.mem_sdiff.mp i.property).1
    have all_bound := integral_componentCharge_le_of_crossing_witnesses s deleted few changed
      (fun i => u i.val) (fun i => v i.val) frame radius (fun i => hu _ (keep i))
      (fun i => hv _ (keep i)) (fun i => not_antipodal _ (keep i)) radius_nonneg radius_small
      integrable not_one
    have u_off : ∀ᵐ g ∂probability, ∀ (i : ↥(s \ deleted)) (j : J),
        inner ℝ (linear (g * frame j) equatorPole) (u i.val) ≠ 0 :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
        ae_not_on_moving_arc_circle (hu _ (keep i)) (frame j)
    have v_off : ∀ᵐ g ∂probability, ∀ (i : ↥(s \ deleted)) (j : J),
        inner ℝ (linear (g * frame j) equatorPole) (v i.val) ≠ 0 :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
        ae_not_on_moving_arc_circle (hv _ (keep i)) (frame j)
    have witness : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
        ∀ i : ↥(s \ deleted), changed g i.val →
        ∃ j, g ∈ arcCrossingEvent (u i.val) (v i.val) (frame j) (radius j) := by
      filter_upwards [hits, u_off, v_off] with g at_g off_u off_v
      intro many i diff
      obtain ⟨j, x, on_side, on_edge⟩ := at_g many i.val (keep i) diff
      have on_network : x ∈ linear g '' (linear (frame j) '' equatorialArc (radius j)) := by
        rw [carrier j, image_closedMinorArc]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_edge)
      exact ⟨j, mem_arcCrossingEvent_of_hit (hu _ (keep i)) (hv _ (keep i))
        (not_antipodal _ (keep i)) (off_u i j) (off_v i j) on_side on_network⟩
    have inequality := all_bound witness
    have sum_length : (∑ j, 2 * radius j) = networkLength endpoint := by
      apply Finset.sum_congr rfl
      intro j _
      change 2 * (length j / 2) = length j
      ring
    rw [sum_length] at inequality
    simpa only [mul_comm, S] using inequality

end Unfoldings.FewestNets
