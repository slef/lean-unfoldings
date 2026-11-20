module

public import Unfoldings.Geometry.MinorArcConnectivity
public import Unfoldings.FewestNets.CrossingChargeBound

/-! Distinct cell labels provide actual Crofton crossings of covered minor arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation
open scoped BigOperators

/-- If disjoint open cells and a framed arc network cover a side whose
endpoints have different labels, the side crosses one of those network arcs
away from the null endpoint incidences. -/
theorem ae_crossing_witness_of_cell_coverage {I J : Type*} [Finite J]
    (cell : SpatialRotation → I → Set Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0) :
    ∀ᵐ g ∂probability, (∀ i, IsOpen (cell g i)) →
      Pairwise (fun i j => Disjoint (cell g i) (cell g j)) →
      closedMinorArc u v ⊆ (⋃ i, cell g i) ∪
        (⋃ j, linear g '' (linear (frame j) '' equatorialArc (radius j))) →
      ∀ {i j : I}, i ≠ j → u ∈ cell g i → v ∈ cell g j →
        ∃ k, g ∈ arcCrossingEvent u v (frame k) (radius k) := by
  have u_off : ∀ᵐ g ∂probability, ∀ k,
      inner ℝ (linear (g * frame k) equatorPole) u ≠ 0 :=
    ae_all_iff.mpr fun k => ae_not_on_moving_arc_circle hu (frame k)
  have v_off : ∀ᵐ g ∂probability, ∀ k,
      inner ℝ (linear (g * frame k) equatorPole) v ≠ 0 :=
    ae_all_iff.mpr fun k => ae_not_on_moving_arc_circle hv (frame k)
  filter_upwards [u_off, v_off] with g hu' hv'
  intro op disjoint covered i j diff left right
  obtain ⟨x, arc, hit⟩ := exists_openMinorArc_mem_network_of_separate (cell g) op disjoint
    hu hv not_antipodal diff left right covered
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hit
  exact ⟨k, mem_arcCrossingEvent_of_hit hu hv not_antipodal (hu' k) (hv' k) arc hk⟩

/-- The expected charge bound for a polygon covered by open cells and the
rotating network. The coverage condition may be restricted to the residual
sides in rotations where the polygon can contribute positive charge. -/
theorem integral_componentCharge_le_of_cell_coverage
    {E I J : Type*} [Finite E] [DecidableEq E] [Fintype J]
    (s deleted : Finset E) (few : deleted.card ≤ 2)
    (changed : SpatialRotation → E → Prop) [∀ g, DecidablePred (changed g)]
    (u v : ↥(s \ deleted) → Space)
    (cell : SpatialRotation → I → Set Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (not_antipodal : ∀ i, u i + v i ≠ 0)
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ Real.pi)
    (integrable : Integrable (fun g => componentCharge (s.filter (changed g)).card) probability)
    (not_one : ∀ᵐ g ∂probability, (s.filter (changed g)).card ≠ 1)
    (op : ∀ᵐ g ∂probability, ∀ i, IsOpen (cell g i))
    (disjoint : ∀ᵐ g ∂probability, Pairwise (fun i j => Disjoint (cell g i) (cell g j)))
    (coverage : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i : ↥(s \ deleted), changed g i.val →
        closedMinorArc (u i) (v i) ⊆ (⋃ k, cell g k) ∪
          (⋃ k, linear g '' (linear (frame k) '' equatorialArc (radius k))))
    (labels : ∀ᵐ g ∂probability, ∀ i : ↥(s \ deleted), changed g i.val →
      ∃ a b, a ≠ b ∧ u i ∈ cell g a ∧ v i ∈ cell g b) :
    (∫ g, componentCharge (s.filter (changed g)).card ∂probability) ≤
      (∑ i, angle (u i) (v i)) * (∑ j, 2 * radius j) / (4 * Real.pi ^ 2) := by
  apply integral_componentCharge_le_of_crossing_witnesses s deleted few changed u v frame radius
    hu hv not_antipodal nonneg small integrable not_one
  have witnesses : ∀ᵐ g ∂probability, ∀ i : ↥(s \ deleted),
      (∀ j, IsOpen (cell g j)) → Pairwise (fun j k => Disjoint (cell g j) (cell g k)) →
      closedMinorArc (u i) (v i) ⊆ (⋃ j, cell g j) ∪
        (⋃ j, linear g '' (linear (frame j) '' equatorialArc (radius j))) →
      ∀ {a b : I}, a ≠ b → u i ∈ cell g a → v i ∈ cell g b →
        ∃ j, g ∈ arcCrossingEvent (u i) (v i) (frame j) (radius j) :=
    ae_all_iff.mpr (fun i =>
      ae_crossing_witness_of_cell_coverage cell frame radius (hu i) (hv i) (not_antipodal i))
  filter_upwards [witnesses, op, disjoint, coverage, labels] with g at_g open_g apart cover assign
  intro many i diff
  obtain ⟨a, b, ab, ha, hb⟩ := assign i diff
  exact at_g i open_g apart (cover many i diff) ab ha hb

end Unfoldings.FewestNets
