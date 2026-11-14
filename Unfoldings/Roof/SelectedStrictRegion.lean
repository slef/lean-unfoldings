module

public import Unfoldings.Roof.PrimalNormalCone
public import Unfoldings.Roof.ClippedStrictRegion
public import Unfoldings.Roof.SelectionIntrinsicDisk

/-! The extension's strict region is precisely the interiors of selected whole-face components. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem interior_selectedCarrier_iff_normal_cell {slopes : Set Plane}
    (convex : Convex ℝ slopes) (compact : IsCompact slopes)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes) (x : Plane) :
    x ∈ interior (K.selectedCarrier slopes) ↔
      x ∈ K.footprint ∧ K.primalNormalCell x ⊆ interior slopes := by
  constructor
  · intro inside
    have in_domain := interior_mono (K.selectedCarrier_subset_footprint slopes) inside
    refine ⟨interior_subset in_domain, ?_⟩
    rw [K.primalNormalCell_eq_incident_hull in_domain]
    apply convexHull_min ?_ convex.interior
    rintro p ⟨f, member, rfl⟩
    have selected := K.selected_of_mem_interior_selectedCarrier inside f member
    by_contra outside
    exact no_boundary f ⟨subset_closure selected, outside⟩
  · rintro ⟨member, cells⟩
    have bounded : Bornology.IsBounded (K.primalNormalCell x) :=
      compact.isBounded.subset (cells.trans interior_subset)
    have inside := K.interior_of_bounded_primalNormalCell member bounded
    have star := eventually_piece_contains_center (fun f => (K.projectedTriangle f).carrier)
      (fun f => (K.projectedTriangle f).compact_carrier.isClosed) x
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [star, isOpen_interior.mem_nhds inside] with y incidence interior
    obtain ⟨f, face⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset (interior_subset interior))
    exact K.mem_selectedCarrier.mpr ⟨f,
      interior_subset (cells (K.original_slope_mem_primalNormalCell f (incidence f face))), face⟩

open Classical in
/-- Every interior point of the selected union lies in the interior of its whole-edge component. -/
theorem interior_selectedCarrier_iff_component {slopes : Set Plane} (x : Plane) :
    x ∈ interior (K.selectedCarrier slopes) ↔ ∃ seed : Face, K.normalSlope seed ∈ slopes ∧
      x ∈ interior (K.restrictedCarrier (K.selectionComponent slopes seed)) := by
  constructor
  · intro inside
    obtain ⟨r, positive, nearby⟩ := Metric.isOpen_iff.mp isOpen_interior x inside
    obtain ⟨f, selected, member⟩ := K.mem_selectedCarrier.mp (interior_subset inside)
    have center : x ∈ Metric.ball x r := Metric.mem_ball_self positive
    have contained := K.region_subset_selectionComponent (convex_ball x r).isPreconnected nearby f
      ⟨x, center, member⟩
    exact ⟨f, selected, Metric.isOpen_ball.subset_interior_iff.mpr contained center⟩
  · rintro ⟨seed, selected, inside⟩
    exact interior_mono (K.selectionComponent_carrier_subset selected) inside

open Classical in
/-- The exact whole-face strict-region identity used in the normal-selection construction. -/
theorem clippedExtension_strict_region_iff_component {slopes : Set Plane}
    (convex : Convex ℝ slopes) (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary_nonempty : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes) (x : Plane) :
    ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary_nonempty).height x <
      (K.clippedExtension slopes compact nonempty).height x ↔
        ∃ seed : Face, K.normalSlope seed ∈ slopes ∧
          x ∈ interior (K.restrictedCarrier (K.selectionComponent slopes seed)) := by
  rw [K.clippedExtension_strict_region_iff compact nonempty boundary_nonempty,
    ← K.interior_selectedCarrier_iff_normal_cell convex compact no_boundary,
    K.interior_selectedCarrier_iff_component]

end Unfoldings.ConvexRoof
