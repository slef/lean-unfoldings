module

public import Unfoldings.Roof.SelectedStrictRegion

/-! A boundary edge of a selected component supplies a common supporting slope at its ends. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {slopes : Set Plane} (seed : Face)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U

open Classical in
/-- A frontier point of a selected component remains on the frontier of the
full selected union, even at a contact between components. -/
theorem selectionComponent_frontier_subset_selected_frontier
    (selected : K.normalSlope seed ∈ slopes) : frontier S ⊆ frontier (K.selectedCarrier slopes) := by
  intro x on_boundary
  have member := (K.compact_restrictedCarrier U).isClosed.frontier_subset on_boundary
  refine (mem_frontier_iff_notMem_interior (K.selectionComponent_carrier_subset selected member)).mpr ?_
  intro global
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp member
  obtain ⟨r, positive, around⟩ := Metric.isOpen_iff.mp isOpen_interior x global
  have ball := K.region_subset_selectionComponent (convex_ball x r).isPreconnected around f.val
    ⟨x, Metric.mem_ball_self positive, face⟩
  have same : K.selectionComponent slopes f.val = U := by
    change {g | (K.selectionGraph slopes).connectedComponentMk g =
      (K.selectionGraph slopes).connectedComponentMk f.val} = _
    rw [show (K.selectionGraph slopes).connectedComponentMk f.val =
      (K.selectionGraph slopes).connectedComponentMk seed from f.property]
    rfl
  rw [same] at ball
  exact on_boundary.2 (Metric.isOpen_ball.subset_interior_iff.mpr ball (Metric.mem_ball_self positive))

/-- At a component frontier point the original normal cell meets the
frontier of the slope selector. This also applies at silhouette edges. -/
theorem selectionComponent_boundary_normal (convex : Convex ℝ slopes)
    (compact : IsCompact slopes) (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (selected : K.normalSlope seed ∈ slopes) {x : Plane} (on_boundary : x ∈ frontier S) :
    ∃ s ∈ frontier slopes, s ∈ K.primalNormalCell x := by
  classical
  have member := (K.compact_restrictedCarrier U).isClosed.frontier_subset on_boundary
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp member
  have in_roof := K.selectedCarrier_subset_footprint slopes (K.selectionComponent_carrier_subset selected member)
  have slope := K.selectionComponent_selected selected f.property
  by_contra! absent
  have interior_slope : K.normalSlope f.val ∈ interior slopes := by
    by_contra outside
    exact no_boundary f.val ⟨subset_closure slope, outside⟩
  have all_inside := convex_subset_interior_of_avoids_frontier (K.convex_primalNormalCell x)
    compact.isClosed (K.original_slope_mem_primalNormalCell f.val face) interior_slope
    (Set.disjoint_left.mpr fun p normal boundary => absent p boundary normal)
  have global := (K.interior_selectedCarrier_iff_normal_cell convex compact no_boundary x).mpr
    ⟨in_roof, all_inside⟩
  exact (K.selectionComponent_frontier_subset_selected_frontier seed selected on_boundary).2 global

end Unfoldings.ConvexRoof
