module

public import Unfoldings.Geometry.MinorArcArclength
public import Unfoldings.Geometry.MinorArcBoundaryCount
public import Unfoldings.Geometry.SphericalSideLocality

/-! Small convex polygons with three changed sides only meet short endpoint portions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

variable {E : Type*} (endpoint : E → Bool → Space)

/-- The carrier of a directed edge in a finite spherical network. The two Boolean indices
are its two endpoints. -/
def networkEdge (i : E) : Set Space :=
  closedMinorArc (endpoint i false) (endpoint i true)

theorem networkEdge_eq_from_endpoint (i : E) (b : Bool) :
    networkEdge endpoint i = closedMinorArc (endpoint i b) (endpoint i (!b)) := by
  cases b
  · rfl
  · exact closedMinorArc_comm _ _

private theorem exists_incident_arclength_of_two_network_hits
    (unit : ∀ i b, ‖endpoint i b‖ = 1)
    (positive : ∀ i, 0 < angle (endpoint i false) (endpoint i true))
    (short : ∀ i, angle (endpoint i false) (endpoint i true) ≤ π / 2)
    {d separation : ℝ} (small : d < separation)
    (separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
      ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, separation ≤ angle x y)
    (cell : Set Space) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    (two_edges : ∃ i j, i ≠ j ∧ (networkEdge endpoint i ∩ cell).Nonempty ∧
      (networkEdge endpoint j ∩ cell).Nonempty)
    {i : E} {x : Space} (on_edge : x ∈ networkEdge endpoint i) (in_cell : x ∈ cell) :
    ∃ (j : E) (a b : Bool) (s t : ℝ), i ≠ j ∧ endpoint i a = endpoint j b ∧
      s ∈ Set.Icc 0 (angle (endpoint i a) (endpoint i (!a))) ∧
      t ∈ Set.Icc 0 (angle (endpoint j b) (endpoint j (!b))) ∧
      let u := minorArcTangent (endpoint i a) (endpoint i (!a))
      let v := minorArcTangent (endpoint j b) (endpoint j (!b))
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ (endpoint i a) u = 0 ∧
      inner ℝ (endpoint i a) v = 0 ∧ angle (endpoint i a) x = s ∧
      angle (greatCirclePoint (endpoint i a) u s) (greatCirclePoint (endpoint i a) v t) ≤ d := by
  classical
  obtain ⟨j, k, separate, j_hits, k_hits⟩ := two_edges
  have another : ∃ j, i ≠ j ∧ (networkEdge endpoint j ∩ cell).Nonempty := by
    by_cases same : i = j
    · exact ⟨k, same.trans_ne separate, k_hits⟩
    · exact ⟨j, same, j_hits⟩
  obtain ⟨j, different, y, on_other, other_in⟩ := another
  have shared : ∃ a b, endpoint i a = endpoint j b := by
    by_contra! apart
    exact (not_le_of_gt small) ((separated different apart x on_edge y on_other).trans
      (diameter x in_cell y other_in))
  obtain ⟨a, b, same_vertex⟩ := shared
  have angles (i : E) (side : Bool) :
      0 < angle (endpoint i side) (endpoint i (!side)) ∧
      angle (endpoint i side) (endpoint i (!side)) ≤ π / 2 := by
    cases side
    · exact ⟨positive i, short i⟩
    · simpa only [Bool.not_true, angle_comm (endpoint i true)] using ⟨positive i, short i⟩
  have arc (i : E) (side : Bool) :=
    closedMinorArc_arclength (unit i side) (unit i (!side)) (angles i side).1
      ((angles i side).2.trans_lt (by linarith [pi_pos]))
  let w := minorArcTangent (endpoint j b) (endpoint j (!b))
  have at_i := arc i a
  have at_j := arc j b
  rw [networkEdge_eq_from_endpoint endpoint i a, at_i.2.2] at on_edge
  rw [networkEdge_eq_from_endpoint endpoint j b, at_j.2.2] at on_other
  obtain ⟨s, hs, px⟩ := on_edge
  obtain ⟨t, ht, py⟩ := on_other
  have w_orthogonal : inner ℝ (endpoint i a) w = 0 := same_vertex.symm ▸ at_j.2.1
  have py' : greatCirclePoint (endpoint i a) w t = y := by
    rw [same_vertex]
    exact py
  have hangle : angle (endpoint i a) x = s := by
    rw [← px]
    exact angle_greatCirclePoint (unit i a) at_i.1 at_i.2.1 hs.1
      ((hs.2.trans (angles i a).2).trans (by linarith [pi_pos]))
  refine ⟨j, a, b, s, t, different, same_vertex, hs, ht, at_i.1, at_j.1,
    at_i.2.1, w_orthogonal, hangle, ?_⟩
  rw [px, py']
  exact diameter x in_cell y other_in

/-- Below the nonincident separation scale, a crossing on any edge lies close to
an endpoint whenever the polygon meets at least two edges of the network. -/
theorem exists_endpoint_angle_le_of_two_network_hits
    (unit : ∀ i b, ‖endpoint i b‖ = 1)
    (positive : ∀ i, 0 < angle (endpoint i false) (endpoint i true))
    (short : ∀ i, angle (endpoint i false) (endpoint i true) ≤ π / 2)
    {d separation ψ : ℝ} (small : d < separation) (ψ_pos : 0 < ψ)
    (separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
      ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, separation ≤ angle x y)
    (incident : ∀ ⦃i j a b⦄, i ≠ j → endpoint i a = endpoint j b →
      ψ ≤ angle (minorArcTangent (endpoint i a) (endpoint i (!a)))
        (minorArcTangent (endpoint j b) (endpoint j (!b))))
    (cell : Set Space) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    (two_edges : ∃ i j, i ≠ j ∧ (networkEdge endpoint i ∩ cell).Nonempty ∧
      (networkEdge endpoint j ∩ cell).Nonempty)
    {i : E} {x : Space} (on_edge : x ∈ networkEdge endpoint i) (in_cell : x ∈ cell) :
    ∃ b, angle (endpoint i b) x ≤ (π / (2 * sin (ψ / 2))) * d := by
  obtain ⟨j, a, b, s, t, distinct, shared, hs, ht, hu, hv, u_orth, v_orth, position, nearby⟩ :=
    exists_incident_arclength_of_two_network_hits endpoint unit positive short small separated
      cell diameter two_edges on_edge in_cell
  have cap (j : E) (b : Bool) : angle (endpoint j b) (endpoint j (!b)) ≤ π / 2 := by
    cases b
    · exact short j
    · simpa only [Bool.not_true, angle_comm (endpoint j true)] using short j
  have corner := incident distinct shared
  have sine_pos : 0 < sin (ψ / 2) := sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [corner.trans (angle_le_pi _ _), pi_pos])
  have localized := greatCirclePoint_endpoint_distance_le (unit i a) hu hv u_orth v_orth
    hs.1 (hs.2.trans (cap i a)) ht.1 (ht.2.trans (cap j b)) ψ_pos corner
  exact ⟨a, position.trans_le (localized.trans
    (mul_le_mul_of_nonneg_left nearby (by positivity)))⟩

/-- Each endpoint has its own cutoff. A point on any side of a polygon meeting
another side is contained in one of its two endpoint portions. -/
theorem exists_endpoint_angle_le_of_two_network_hits_sharp
    (unit : ∀ i b, ‖endpoint i b‖ = 1)
    (positive : ∀ i, 0 < angle (endpoint i false) (endpoint i true))
    {L d separation : ℝ} (L_pos : 0 < L) (L_small : L ≤ π / 2)
    (short : ∀ i, angle (endpoint i false) (endpoint i true) ≤ L) (small : d < separation)
    (separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
      ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, separation ≤ angle x y)
    (ψ : E → Bool → ℝ) (ψ_pos : ∀ i a, 0 < ψ i a)
    (incident : ∀ ⦃i j a b⦄, i ≠ j → endpoint i a = endpoint j b →
      ψ i a ≤ angle (minorArcTangent (endpoint i a) (endpoint i (!a)))
        (minorArcTangent (endpoint j b) (endpoint j (!b))))
    (cell : Set Space) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    (two_edges : ∃ i j, i ≠ j ∧ (networkEdge endpoint i ∩ cell).Nonempty ∧
      (networkEdge endpoint j ∩ cell).Nonempty)
    {i : E} {x : Space} (on_edge : x ∈ networkEdge endpoint i) (in_cell : x ∈ cell) :
    ∃ a, angle (endpoint i a) x ≤ L / (sin L * sin (min (ψ i a) (π / 2))) * d := by
  obtain ⟨j, a, b, s, t, distinct, shared, hs, ht, hu, hv, u_orth, v_orth, position, nearby⟩ :=
    exists_incident_arclength_of_two_network_hits endpoint unit positive
      (fun i => (short i).trans L_small) small separated cell diameter two_edges on_edge in_cell
  have cap (j : E) (b : Bool) : angle (endpoint j b) (endpoint j (!b)) ≤ L := by
    cases b
    · exact short j
    · simpa only [Bool.not_true, angle_comm (endpoint j true)] using short j
  have sineL : 0 < sin L :=
    sin_pos_of_pos_of_lt_pi L_pos (by linarith only [L_small, pi_pos])
  have sineψ : 0 < sin (min (ψ i a) (π / 2)) :=
    sin_pos_of_pos_of_lt_pi (lt_min (ψ_pos i a) pi_div_two_pos)
      ((min_le_right _ _).trans_lt (by linarith only [pi_pos]))
  have localized := greatCirclePoint_incident_side_bound (unit i a) hu hv u_orth v_orth hs.1
    (hs.2.trans (cap i a)) L_pos L_small ht.1 ((ht.2.trans (cap j b)).trans L_small)
    (ψ_pos i a) (incident distinct shared)
  exact ⟨a, position.trans_le (localized.trans
    (mul_le_mul_of_nonneg_left nearby (by positivity)))⟩

/-- With three changed sides and transverse hits on their disjoint relative interiors,
a convex polygon must meet at least two distinct network edges. -/
theorem exists_two_network_hits_of_three_boundary_hits {F I : Type*}
    (unit : ∀ i b, ‖endpoint i b‖ = 1)
    (not_antipodal : ∀ i, endpoint i false + endpoint i true ≠ 0)
    (f : I → Space →ₗ[ℝ] ℝ)
    (transverse : ∀ e i, f i (endpoint e false) ≠ 0 ∨ f i (endpoint e true) ≠ 0)
    (s : Finset F) (many : 3 ≤ s.card) (p q : F → Space)
    (apart : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (openMinorArc (p a) (q a))
      (openMinorArc (p b) (q b)))
    (hits : ∀ a ∈ s, ∃ e x, x ∈ openMinorArc (endpoint e false) (endpoint e true) ∧
      x ∈ openMinorArc (p a) (q a) ∧ (∀ i, 0 ≤ f i x) ∧ ∃ i, f i x = 0) :
    ∃ i j, i ≠ j ∧
      (networkEdge endpoint i ∩ {x | ∀ k, 0 ≤ f k x}).Nonempty ∧
      (networkEdge endpoint j ∩ {x | ∀ k, 0 ≤ f k x}).Nonempty := by
  classical
  have nonempty : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := nonempty
  obtain ⟨e, x, on_e, on_a, inside, zero⟩ := hits a ha
  have e_hits : (networkEdge endpoint e ∩ {x | ∀ k, 0 ≤ f k x}).Nonempty :=
    ⟨x, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_e), inside⟩
  by_contra! single
  let boundary := openMinorArc (endpoint e false) (endpoint e true) ∩
    {y | (∀ k, 0 ≤ f k y) ∧ ∃ k, f k y = 0}
  have contact (b : s) : ∃ y : boundary, y.val ∈ openMinorArc (p b.val) (q b.val) := by
    obtain ⟨j, y, on_j, on_b, in_b, some_zero⟩ := hits b.val b.property
    have equal : j = e := by
      by_contra unequal
      have j_hits : (networkEdge endpoint j ∩ {x | ∀ k, 0 ≤ f k x}).Nonempty :=
        ⟨y, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_j), in_b⟩
      exact j_hits.ne_empty (single e j (Ne.symm unequal) e_hits)
    subst j
    exact ⟨⟨y, on_j, in_b, some_zero⟩, on_b⟩
  choose point point_on using contact
  have injective : Function.Injective point := by
    intro a b equal
    by_contra distinct
    exact Set.disjoint_left.mp (apart a.val a.property b.val b.property
      (fun same => distinct (Subtype.ext same))) (point_on a) (equal.symm ▸ point_on b)
  have count : ENat.card s ≤ ENat.card boundary := ENat.card_le_card_of_injective injective
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe, ENat.card_coe_set_eq] at count
  have upper := encard_openMinorArc_support_boundary_le (unit e false) (unit e true)
    (not_antipodal e) f (transverse e)
  have impossible := count.trans upper
  norm_cast at impossible
  omega

end Unfoldings.FewestNets
