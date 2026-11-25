module

public import Unfoldings.Geometry.ArcFamilyCrofton
public import Unfoldings.Geometry.SphericalArcEndpointClip
public import Unfoldings.FewestNets.SingleCellReflections

/-! Signed Gaussian polygon charges are bounded by a quarter of the residual crossing count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory InnerProductGeometry SpatialRotation Real

variable {I J : Type*} [Fintype I] [Fintype J]
  (charge : SpatialRotation → ℝ) (remaining : Set SpatialRotation)
  (changed : SpatialRotation → I → Prop) [∀ g, DecidablePred (changed g)]
  (u v : I → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
  (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (nonantipodal : ∀ i, u i + v i ≠ 0)
  (integrable : Integrable charge probability) (measurable : MeasurableSet remaining)
  (pointwise : ∀ᵐ g ∂probability, g ∈ remaining →
    charge g ≤ (∑ i, if changed g i then (1 : ℝ) else 0) / 4)

include hu hv nonantipodal integrable measurable pointwise in
/-- On the orientations still to be counted, a witness per changed side yields
the signed residual charge bound. Discarded orientations carry zero in this integral. -/
theorem integral_singleCellCharge_le_of_crossing_witnesses
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ π)
    (witness : ∀ᵐ g ∂probability, g ∈ remaining →
      ∀ i, changed g i → ∃ j, g ∈ arcCrossingEvent (u i) (v i) (frame j) (radius j)) :
    (∫ g in remaining, charge g ∂probability) ≤
      (∑ i, angle (u i) (v i)) * (∑ j, 2 * radius j) / (8 * π ^ 2) := by
  have each (i : I) (j : J) (g : SpatialRotation) :
      0 ≤ (arcCrossingEvent (u i) (v i) (frame j) (radius j)).indicator (fun _ => (1 : ℝ)) g :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have estimate : ∀ᵐ g ∂probability, remaining.indicator charge g ≤
      (1 / 4 : ℝ) * arcFamilyCrossings u v frame radius g := by
    filter_upwards [pointwise, witness] with g upper hit
    have total_nonneg : 0 ≤ arcFamilyCrossings u v frame radius g :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => each i j g))
    by_cases member : g ∈ remaining
    · rw [Set.indicator_of_mem member]
      have count : (∑ i, if changed g i then (1 : ℝ) else 0) ≤
          arcFamilyCrossings u v frame radius g := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with across
        · obtain ⟨j, crosses⟩ := hit member i across
          have term := Finset.single_le_sum (f := fun k : J =>
            (arcCrossingEvent (u i) (v i) (frame k) (radius k)).indicator (fun _ => (1 : ℝ)) g)
            (fun k _ => each i k g) (Finset.mem_univ j)
          simpa only [Set.indicator_of_mem crosses] using term
        · exact Finset.sum_nonneg (fun j _ => each i j g)
      linarith only [upper member, count]
    · rw [Set.indicator_of_notMem member]
      exact mul_nonneg (by norm_num) total_nonneg
  rw [← integral_indicator measurable]
  have compare := integral_mono_ae (integrable.indicator measurable)
    ((integrable_arcFamilyCrossings u v frame radius hu hv nonantipodal).const_mul (1 / 4))
    estimate
  rw [integral_const_mul, integral_arcFamilyCrossings u v frame radius
    hu hv nonantipodal nonneg small] at compare
  convert compare using 1 <;> ring


include hu hv nonantipodal integrable measurable pointwise in
/-- Each of the two endpoints of each selector side may have its own reach. -/
theorem integral_singleCellCharge_le_of_endpoint_witnesses
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ π / 2)
    (reach : J × Bool → ℝ) (reach_nonneg : ∀ j, 0 ≤ reach j)
    (witness : ∀ᵐ g ∂probability, g ∈ remaining →
      ∀ i, changed g i → ∃ (j : J × Bool) (x : Space),
        x ∈ openMinorArc (u i) (v i) ∧
        x ∈ linear g '' (linear (frame j.1) '' equatorialArc (radius j.1)) ∧
        angle (linear g (linear (frame j.1) (equatorPoint
          ((arcEndpointPhase (radius j.1) j.2 : ℝ) : EquatorPhase)))) x ≤ reach j) :
    (∫ g in remaining, charge g ∂probability) ≤
      (∑ i, angle (u i) (v i)) * (∑ j, reach j) / (8 * π ^ 2) := by
  let clipFrame (j : J × Bool) := endpointClipFrame (frame j.1) (radius j.1) (reach j) j.2
  let clipRadius (j : J × Bool) := endpointClipRadius (radius j.1) (reach j)
  have clip_nonneg (j : J × Bool) : 0 ≤ clipRadius j :=
    endpointClipRadius_nonneg (nonneg j.1) (reach_nonneg j)
  have clip_small (j : J × Bool) : clipRadius j ≤ π :=
    (min_le_left _ _).trans ((small j.1).trans (by linarith only [pi_pos]))
  have off_u : ∀ᵐ g ∂probability, ∀ (i : I) (j : J × Bool),
      inner ℝ (linear (g * clipFrame j) equatorPole) (u i) ≠ 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_not_on_moving_arc_circle (hu i) _
  have off_v : ∀ᵐ g ∂probability, ∀ (i : I) (j : J × Bool),
      inner ℝ (linear (g * clipFrame j) equatorPole) (v i) ≠ 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_not_on_moving_arc_circle (hv i) _
  have clipped : ∀ᵐ g ∂probability, g ∈ remaining → ∀ i, changed g i →
      ∃ j, g ∈ arcCrossingEvent (u i) (v i) (clipFrame j) (clipRadius j) := by
    filter_upwards [witness, off_u, off_v] with g found u_off v_off
    intro member i changed_i
    obtain ⟨j, x, on_i, ⟨y, on_j, rfl⟩, close⟩ := found member i changed_i
    have near : angle (linear (frame j.1) (equatorPoint
        ((arcEndpointPhase (radius j.1) j.2 : ℝ) : EquatorPhase))) y ≤ reach j := by
      change angle ((isometry g).toLinearIsometry _) ((isometry g).toLinearIsometry _) ≤ _ at close
      rwa [(isometry g).toLinearIsometry.angle_map] at close
    have on_clip := mem_endpointClip_of_angle_le (nonneg j.1) (small j.1) (reach_nonneg j)
      on_j near
    exact ⟨j, mem_arcCrossingEvent_of_hit (hu i) (hv i) (nonantipodal i)
      (u_off i j) (v_off i j) on_i ⟨y, on_clip, rfl⟩⟩
  have estimate := integral_singleCellCharge_le_of_crossing_witnesses charge remaining changed
    u v clipFrame clipRadius hu hv nonantipodal integrable measurable pointwise
    clip_nonneg clip_small clipped
  have sum_clips : (∑ j, 2 * clipRadius j) ≤ ∑ j, reach j :=
    Finset.sum_le_sum fun j _ => two_mul_endpointClipRadius_le (radius j.1) (reach j)
  exact estimate.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sum_clips
    (Finset.sum_nonneg fun i _ => angle_nonneg (u i) (v i))) (by positivity))

end Unfoldings.FewestNets
