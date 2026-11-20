module

public import Unfoldings.Geometry.MinorArcConnectivity
public import Unfoldings.FewestNets.CrossingChargeBound

/-! Distinct cell labels provide actual Crofton crossings of covered minor arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation

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

end Unfoldings.FewestNets
