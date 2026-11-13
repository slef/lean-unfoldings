module

public import Unfoldings.Roof.GradientSelection
public import Unfoldings.Roof.Topology
public import Unfoldings.Topology.EscapeRays

/-! Convex-gradient selections have connected planar complement and no bounded holes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The closed union of the projected faces whose normal slopes belong to the selection. -/
def selectedCarrier (slopes : Set Plane) : Set Plane :=
  ⋃ f : {f : Face // K.normalSlope f ∈ slopes}, (K.projectedTriangle f.val).carrier

@[simp] theorem mem_selectedCarrier {slopes : Set Plane} {p : Plane} :
    p ∈ K.selectedCarrier slopes ↔
      ∃ f : Face, K.normalSlope f ∈ slopes ∧ p ∈ (K.projectedTriangle f).carrier := by
  simp only [selectedCarrier, Set.mem_iUnion, Subtype.exists, exists_prop]

/-- Every gradient selection is compact because the input roof has finitely many faces. -/
theorem compact_selectedCarrier (slopes : Set Plane) : IsCompact (K.selectedCarrier slopes) :=
  isCompact_iUnion fun f => (K.projectedTriangle f.val).compact_carrier

theorem selectedCarrier_subset_footprint (slopes : Set Plane) :
    K.selectedCarrier slopes ⊆ K.footprint := by
  intro p member
  obtain ⟨f, _, inside⟩ := K.mem_selectedCarrier.mp member
  rw [K.footprint_eq_union_projectedTriangles]
  exact Set.mem_iUnion.mpr ⟨f, inside⟩

/-- Every point omitted by a closed convex gradient selection escapes to infinity along
one straight ray. The starting point may lie on a face edge or outside the roof. -/
theorem exists_selectedCarrier_escape {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (nonempty : slopes.Nonempty)
    {p : Plane} (outside : p ∉ K.selectedCarrier slopes) :
    ∃ u : Plane, u ≠ 0 ∧ ∀ r : ℝ, 0 ≤ r → p + r • u ∉ K.selectedCarrier slopes := by
  by_cases in_roof : p ∈ K.footprint
  · have covered := in_roof
    rw [K.footprint_eq_union_projectedTriangles, Set.mem_iUnion] at covered
    obtain ⟨f, inside⟩ := covered
    have omitted : K.normalSlope f ∉ slopes := by
      intro selected
      exact outside (K.mem_selectedCarrier.mpr ⟨f, selected, inside⟩)
    rw [projectedTriangle, Triangle.affineImage_carrier] at inside
    obtain ⟨x, hx, image⟩ := inside
    obtain ⟨u, nonzero, escape⟩ :=
      K.exists_gradient_selection_escape convex closed nonempty f omitted ⟨x, hx⟩
    refine ⟨u, nonzero, ?_⟩
    intro r nonnegative member
    by_cases zero : r = 0
    · apply outside
      simpa only [zero, zero_smul, add_zero] using member
    · obtain ⟨g, selected, inside⟩ := K.mem_selectedCarrier.mp member
      exact escape r (lt_of_le_of_ne nonnegative (Ne.symm zero)) g selected
        (by simpa [image] using inside)
  · obtain ⟨u, nonzero, escape⟩ :=
      PlanarTopology.exists_escape_ray_of_not_mem_closed_convex K.convex_projection
        K.compact_footprint.isClosed (K.interior_projection.mono interior_subset) in_roof
    exact ⟨u, nonzero, fun r hr h => escape r hr (K.selectedCarrier_subset_footprint slopes h)⟩

/-- A closed convex selection of roof gradients leaves no bounded complementary region. -/
theorem isConnected_compl_selectedCarrier {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (nonempty : slopes.Nonempty) :
    IsConnected (K.selectedCarrier slopes)ᶜ :=
  PlanarTopology.isConnected_compl_of_escape_rays (K.compact_selectedCarrier slopes)
    (fun _ outside => K.exists_selectedCarrier_escape convex closed nonempty outside)

/-- Every bounded region enclosed by selected faces is itself selected. -/
theorem inside_subset_selectedCarrier {slopes J : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (nonempty : slopes.Nonempty)
    (subset : J ⊆ K.selectedCarrier slopes) : Schoenflies.inside J ⊆ K.selectedCarrier slopes :=
  PlanarTopology.inside_subset_of_isConnected_compl (K.compact_selectedCarrier slopes)
    (K.isConnected_compl_selectedCarrier convex closed nonempty) subset

end Unfoldings.ConvexRoof
