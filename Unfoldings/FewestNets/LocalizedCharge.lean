module

public import Unfoldings.FewestNets.EndpointCrossingBudget
public import Unfoldings.FewestNets.EndpointCrossingLocality

/-! The small-diameter case of the expected component count for a fixed network. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation Real

/-- A convex spherical polygon below the network separation scale satisfies
the local expected charge bound. The crossing witnesses record interior hits
of the changed polygon sides with the moving network. -/
theorem integral_componentCharge_le_of_small_diameter
    {E J I : Type*} [Finite E] [DecidableEq E] [Fintype J] [Finite I]
    (s deleted : Finset E) (few : deleted.card ≤ 2)
    (changed : SpatialRotation → E → Prop) [∀ g, DecidablePred (changed g)]
    (p q : E → Space) (hp : ∀ i ∈ s, ‖p i‖ = 1) (hq : ∀ i ∈ s, ‖q i‖ = 1)
    (not_antipodal : ∀ i ∈ s, p i + q i ≠ 0)
    (f : I → Space →L[ℝ] ℝ) (f_ne : ∀ i, f i ≠ 0)
    (boundary : ∀ i ∈ s, ∀ x ∈ openMinorArc (p i) (q i),
      (∀ k, 0 ≤ f k x) ∧ ∃ k, f k x = 0)
    (apart : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      Disjoint (openMinorArc (p a) (q a)) (openMinorArc (p b) (q b)))
    {d separation ψ : ℝ} (d_nonneg : 0 ≤ d) (small : d < separation)
    (ψ_pos : 0 < ψ) (ψ_le : ψ ≤ π)
    (diameter : ∀ x, ‖x‖ = 1 → (∀ k, 0 ≤ f k x) →
      ∀ y, ‖y‖ = 1 → (∀ k, 0 ≤ f k y) → angle x y ≤ d)
    (endpoint : J → Bool → Space) (unit : ∀ j b, ‖endpoint j b‖ = 1)
    (positive : ∀ j, 0 < angle (endpoint j false) (endpoint j true))
    (short : ∀ j, angle (endpoint j false) (endpoint j true) ≤ π / 2)
    (separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
      ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, separation ≤ angle x y)
    (incident : ∀ ⦃i j a b⦄, i ≠ j → endpoint i a = endpoint j b →
      ψ ≤ angle (minorArcTangent (endpoint i a) (endpoint i (!a)))
        (minorArcTangent (endpoint j b) (endpoint j (!b))))
    (integrable : Integrable (fun g => componentCharge (s.filter (changed g)).card) probability)
    (not_one : ∀ᵐ g ∂probability, (s.filter (changed g)).card ≠ 1)
    (hits : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i ∈ s, changed g i → ∃ j x, x ∈ openMinorArc (p i) (q i) ∧
        x ∈ openMinorArc (linear g (endpoint j false)) (linear g (endpoint j true))) :
    (∫ g, componentCharge (s.filter (changed g)).card ∂probability) ≤
      Fintype.card J * ((∑ i : ↥(s \ deleted), angle (p i.val) (q i.val)) * d) /
        (4 * π * sin (ψ / 2)) := by
  let length (j : J) := angle (endpoint j false) (endpoint j true)
  let radius (j : J) := length j / 2
  choose frame carrier endpoints using fun j =>
    exists_frame_closedMinorArc_with_endpoints (unit j false) (unit j true)
      (positive j) ((short j).trans_lt (by linarith [pi_pos]))
  have framed (j : J) : linear (frame j) '' equatorialArc (radius j) = networkEdge endpoint j :=
    carrier j
  have positioned (j : J) (b : Bool) :
      linear (frame j) (equatorPoint ((arcEndpointPhase (radius j) b : ℝ) : EquatorPhase)) =
        endpoint j b := by
    cases b <;> exact endpoints j _
  have nondegenerate (j : J) : endpoint j false + endpoint j true ≠ 0 := by
    intro zero
    have left : endpoint j false ≠ 0 := by
      intro h
      have := unit j false
      rw [h, norm_zero] at this
      norm_num at this
    have opposite : endpoint j true = -endpoint j false := eq_neg_of_add_eq_zero_right zero
    have bound := short j
    rw [opposite, angle_self_neg_of_nonzero left] at bound
    linarith [pi_pos]
  have generic := ae_avoids_finite_hyperplanes (fun j => endpoint j false) (fun j => unit j false)
    f f_ne
  have sine_pos : 0 < sin (ψ / 2) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  let reach := (π / (2 * sin (ψ / 2))) * d
  have reach_nonneg : 0 ≤ reach := by dsimp [reach]; positivity
  have residual (i : ↥(s \ deleted)) : i.val ∈ s := (Finset.mem_sdiff.mp i.property).1
  have estimate := integral_componentCharge_le_of_endpoint_hits s deleted few changed
    (fun i => p i.val) (fun i => q i.val) frame radius reach_nonneg
    (fun i => hp i.val (residual i)) (fun i => hq i.val (residual i))
    (fun i => not_antipodal i.val (residual i))
    (fun j => div_nonneg (positive j).le (by norm_num))
    (fun j => by dsimp [radius, length]; linarith [short j, pi_pos]) integrable not_one
  have equation :
      (∑ i : ↥(s \ deleted), angle (p i.val) (q i.val)) *
        (2 * Fintype.card J * reach) / (4 * π ^ 2) =
      Fintype.card J * ((∑ i : ↥(s \ deleted), angle (p i.val) (q i.val)) * d) /
        (4 * π * sin (ψ / 2)) := by
    dsimp [reach]
    field_simp [pi_ne_zero, sine_pos.ne']
  rw [← equation]
  apply estimate
  filter_upwards [hits, generic] with g at_g trans_g
  intro many i changed_i
  let moved (j : J) (b : Bool) := linear g (endpoint j b)
  let cone : Set Space := {x | ∀ k, 0 ≤ f k x}
  let cell : Set Space := {x | ‖x‖ = 1 ∧ x ∈ cone}
  have rotate_angle (x y : Space) : angle (linear g x) (linear g y) = angle x y :=
    (isometry g).toLinearIsometry.angle_map x y
  have moved_carrier (j : J) : networkEdge moved j = linear g '' networkEdge endpoint j :=
    (image_closedMinorArc g _ _).symm
  have move_tangent (j : J) (b : Bool) :
      minorArcTangent (moved j b) (moved j (!b)) =
        linear g (minorArcTangent (endpoint j b) (endpoint j (!b))) := by
    simp only [moved, minorArcTangent, rotate_angle, map_smul, map_sub]
  have moved_unit (j b) : ‖moved j b‖ = 1 :=
    ((isometry g).norm_map _).trans (unit j b)
  have moved_apart (j) : moved j false + moved j true ≠ 0 := by
    intro h
    apply nondegenerate j
    apply (isometry g).injective
    change linear g _ = linear g 0
    simp only [map_add, map_zero]
    exact h
  have moved_separation ⦃j k : J⦄ (distinct : j ≠ k)
      (not_incident : ∀ a b, moved j a ≠ moved k b) :
      ∀ x ∈ networkEdge moved j, ∀ y ∈ networkEdge moved k, separation ≤ angle x y := by
    intro x hx y hy
    rw [moved_carrier] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [rotate_angle]
    exact separated distinct (fun a b same => not_incident a b (congrArg (linear g) same))
      x₀ hx₀ y₀ hy₀
  have moved_incidence ⦃j k : J⦄ ⦃a b : Bool⦄ (distinct : j ≠ k)
      (shared : moved j a = moved k b) :
      ψ ≤ angle (minorArcTangent (moved j a) (moved j (!a)))
        (minorArcTangent (moved k b) (moved k (!b))) := by
    rw [move_tangent, move_tangent, rotate_angle]
    exact incident distinct ((isometry g).injective shared)
  have unit_on_edge (j : J) (z : Space) (on_edge : z ∈ networkEdge moved j) :
      ‖z‖ = 1 := by
    have in_sphere := closedMinorArc_subset_sphere (moved_unit j false) (moved_unit j true)
      (moved_apart j) on_edge
    simpa only [Metric.mem_sphere, dist_zero_right] using in_sphere
  have two_cone_edges : ∃ j k, j ≠ k ∧ (networkEdge moved j ∩ cone).Nonempty ∧
      (networkEdge moved k ∩ cone).Nonempty := by
    apply exists_two_network_hits_of_three_boundary_hits moved moved_unit moved_apart
      (fun i => (f i).toLinearMap) (fun j k => Or.inl (trans_g j k))
      (s.filter (changed g)) many p q
    · intro a ha b hb distinct
      exact apart a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 distinct
    · intro a ha
      obtain ⟨mem, changed_a⟩ := Finset.mem_filter.mp ha
      obtain ⟨j, x, on_a, on_j⟩ := at_g many a mem changed_a
      exact ⟨j, x, on_j, on_a, boundary a mem x on_a⟩
  have two_edges : ∃ j k, j ≠ k ∧ (networkEdge moved j ∩ cell).Nonempty ∧
      (networkEdge moved k ∩ cell).Nonempty := by
    obtain ⟨j, k, distinct, ⟨x, x_edge, x_cone⟩, ⟨y, y_edge, y_cone⟩⟩ := two_cone_edges
    exact ⟨j, k, distinct, ⟨x, x_edge, unit_on_edge j x x_edge, x_cone⟩,
      ⟨y, y_edge, unit_on_edge k y y_edge, y_cone⟩⟩
  obtain ⟨j, x, on_i, on_j⟩ := at_g many i.val (residual i) changed_i
  have on_edge : x ∈ networkEdge moved j :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_j)
  have localized := exists_endpoint_angle_le_of_two_network_hits moved moved_unit
    (fun j => by simpa only [moved, rotate_angle] using positive j)
    (fun j => by simpa only [moved, rotate_angle] using short j)
    small ψ_pos moved_separation moved_incidence cell
    (fun a ha b hb => diameter a ha.1 ha.2 b hb.1 hb.2) two_edges on_edge
    ⟨unit_on_edge j x on_edge, (boundary i.val (residual i) x on_i).1⟩
  obtain ⟨b, near⟩ := localized
  refine ⟨j, b, x, on_i, ?_, ?_⟩
  · rwa [framed, ← moved_carrier]
  · rwa [positioned]

end Unfoldings.FewestNets
