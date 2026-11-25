module

public import Unfoldings.FewestNets.SingleCellReflections
public import Unfoldings.FewestNets.EndpointCrossingLocality
public import Mathlib.Topology.Maps.Proper.Basic

/-! Strict central-hit conditions form measurable sets of orientations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- A continuous family of open-interval arcs meets a closed set on a
measurable parameter set. Each smaller closed interval gives a closed hit set. -/
theorem measurableSet_open_interval_hit {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (evaluate : X × ℝ → Y) (continuous_evaluate : Continuous evaluate)
    (region : Set Y) (closed : IsClosed region) (a b : ℝ) :
    MeasurableSet {x : X | ∃ t ∈ Set.Ioo a b, evaluate (x, t) ∈ region} := by
  let reach (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let small (n : ℕ) : Set ℝ := Set.Icc (a + reach n) (b - reach n)
  let hits (n : ℕ) : Set X := {x | ∃ t ∈ small n, evaluate (x, t) ∈ region}
  have closed_hits (n : ℕ) : IsClosed (hits n) := by
    letI : CompactSpace (small n) := isCompact_iff_compactSpace.mp isCompact_Icc
    let contact : Set (X × small n) := {p | evaluate (p.1, p.2.val) ∈ region}
    have contact_closed : IsClosed contact :=
      closed.preimage (continuous_evaluate.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    have project : Prod.fst '' contact = hits n := by
      ext x
      constructor
      · rintro ⟨⟨_, t⟩, member, rfl⟩
        exact ⟨t.val, t.property, member⟩
      · rintro ⟨t, ht, hx⟩
        exact ⟨⟨x, ⟨t, ht⟩⟩, hx, rfl⟩
    rw [← project]
    exact isClosedMap_fst_of_compactSpace contact contact_closed
  have union : {x : X | ∃ t ∈ Set.Ioo a b, evaluate (x, t) ∈ region} = ⋃ n, hits n := by
    ext x
    constructor
    · rintro ⟨t, ⟨first, last⟩, hit⟩
      obtain ⟨n, near⟩ := exists_nat_one_div_lt (lt_min (sub_pos.mpr first) (sub_pos.mpr last))
      have near' : reach n < t - a ∧ reach n < b - t := lt_min_iff.mp near
      exact Set.mem_iUnion.mpr ⟨n, t, ⟨by linarith only [near'.1], by linarith only [near'.2]⟩, hit⟩
    · intro member
      obtain ⟨n, t, ht, hit⟩ := Set.mem_iUnion.mp member
      have positive : 0 < reach n := by dsimp only [reach]; positivity
      exact ⟨t, ⟨by linarith only [ht.1, positive], by linarith only [ht.2, positive]⟩, hit⟩
  rw [union]
  exact MeasurableSet.iUnion fun n => (closed_hits n).measurableSet

open SpatialRotation

/-- The orientations whose placed arc meets the cell strictly between the two cuts. -/
def centralOrientations (region : Set Space) (arc : ℝ → Space) (a b : ℝ) (reversed : Bool) :
    Set SpatialRotation :=
  {g | ∃ t ∈ Set.Ioo a b, orthogonalPlacement g reversed (arc t) ∈ region}

theorem centralOrientations_measurable (region : Set Space) (closed : IsClosed region)
    (arc : ℝ → Space) (continuous_arc : Continuous arc) (a b : ℝ) (reversed : Bool) :
    MeasurableSet (centralOrientations region arc a b reversed) := by
  apply measurableSet_open_interval_hit
    (fun p => orthogonalPlacement p.1 reversed (arc p.2)) _ region closed a b
  have move : Continuous (fun p : SpatialRotation × ℝ => linear p.1 (arc p.2)) :=
    SpatialRotation.continuous_apply.comp (continuous_fst.prodMk
      (continuous_arc.comp continuous_snd))
  cases reversed
  · exact move
  · exact move.neg

/-- Reflection in the whole side plane preserves this set and keeps each
individual cutoff, even for asymmetrically clipped sides. -/
theorem exists_reflection_stable_centralOrientations (region : Set Space)
    (arc : ℝ → Space) (a b : ℝ) {normal : Space} (nonzero : normal ≠ 0)
    (on_plane : ∀ t ∈ Set.Ioo a b, inner ℝ normal (arc t) = 0) :
    ∃ flip : SpatialRotation, ∀ g reversed,
      g ∈ centralOrientations region arc a b reversed ↔
        g * flip ∈ centralOrientations region arc a b (!reversed) := by
  obtain ⟨flip, reflects⟩ := exists_plane_reflection_placement nonzero
  refine ⟨flip, fun g reversed => ?_⟩
  have fixes (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      orthogonalPlacement (g * flip) (!reversed) (arc t) =
        orthogonalPlacement g reversed (arc t) := by
    rw [reflects]
    have member : arc t ∈ (ℝ ∙ normal)ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (on_plane t ht)
    rw [Submodule.reflection_mem_subspace_eq_self member]
  constructor
  · rintro ⟨t, ht, contact⟩
    exact ⟨t, ht, (fixes t ht).symm ▸ contact⟩
  · rintro ⟨t, ht, contact⟩
    exact ⟨t, ht, (fixes t ht) ▸ contact⟩

open InnerProductGeometry Real

/-- A hit farther from both endpoints than their own cutoffs excludes any
hit on a second template side in a cell below the separation scale. -/
theorem centralSide_disjoint_other_network_edges {J : Type*} (endpoint : J → Bool → Space)
    (unit : ∀ i b, ‖endpoint i b‖ = 1)
    (positive : ∀ i, 0 < angle (endpoint i false) (endpoint i true))
    {L d s : ℝ} (L_pos : 0 < L) (L_small : L ≤ π / 2)
    (short : ∀ i, angle (endpoint i false) (endpoint i true) ≤ L) (small : d < s)
    (separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
      ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, s ≤ angle x y)
    (psi : J → Bool → ℝ) (psi_pos : ∀ i a, 0 < psi i a)
    (incident : ∀ ⦃i j a b⦄, i ≠ j → endpoint i a = endpoint j b →
      psi i a ≤ angle (minorArcTangent (endpoint i a) (endpoint i (!a)))
        (minorArcTangent (endpoint j b) (endpoint j (!b))))
    (cell : Set Space) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    {i : J} {x : Space} (on_side : x ∈ networkEdge endpoint i) (inside : x ∈ cell)
    (central : ∀ a, L / (sin L * sin (min (psi i a) (π / 2))) * d < angle (endpoint i a) x)
    {j : J} (different : i ≠ j) :
    Disjoint (networkEdge endpoint j) cell := by
  rw [Set.disjoint_left]
  intro y on_other inside_other
  obtain ⟨a, close⟩ := exists_endpoint_angle_le_of_two_network_hits_sharp endpoint unit positive
    L_pos L_small short small separated psi psi_pos incident cell diameter
    ⟨i, j, different, ⟨x, on_side, inside⟩, ⟨y, on_other, inside_other⟩⟩ on_side inside
  exact (central a).not_ge close

end Unfoldings.FewestNets
