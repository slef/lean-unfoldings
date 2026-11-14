module

public import Unfoldings.Roof.DualFace
public import Unfoldings.Convex.BoundaryPotential
public import Unfoldings.Topology.ConvexFrontier

/-! Exact strict-region identification for the clipped extension and boundary potential. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem clippedExtension_active_iff_original {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) {x p : Plane}
    (member : x ∈ K.footprint)
    (height : (K.clippedExtension slopes compact nonempty).height x = -K.roofHeight x) :
    (K.clippedExtension slopes compact nonempty).Active x p ↔
      p ∈ slopes ∧ p ∈ K.primalNormalCell x := by
  rw [K.primalNormalCell_iff_dual member]
  change p ∈ slopes ∧ (K.clippedExtension slopes compact nonempty).height x =
    inner ℝ x p - K.dualCost p ↔ _
  rw [height]
  constructor <;> rintro ⟨hp, equal⟩ <;> refine ⟨hp, ?_⟩ <;> linarith

theorem clippedExtension_eq_original_of_normal {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) {x p : Plane}
    (member : x ∈ K.footprint) (normal : p ∈ K.primalNormalCell x) (selected : p ∈ slopes) :
    (K.clippedExtension slopes compact nonempty).height x = -K.roofHeight x := by
  let E := K.clippedExtension slopes compact nonempty
  apply le_antisymm
  · exact E.height_le (fun q _ => K.fenchel_inequality member q)
  · have lower := E.affine_le x selected
    change inner ℝ x p - K.dualCost p ≤ E.height x at lower
    rw [(K.primalNormalCell_iff_dual member p).mp normal] at lower
    linarith

/-- The strict difference region is exactly the original domain points whose full primal
normal cell lies in the interior of the clipping set. This includes all rim normal cones. -/
theorem clippedExtension_strict_region_iff {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary_nonempty : (frontier slopes).Nonempty) (x : Plane) :
    ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary_nonempty).height x <
      (K.clippedExtension slopes compact nonempty).height x ↔
        x ∈ K.footprint ∧ K.primalNormalCell x ⊆ interior slopes := by
  let E := K.clippedExtension slopes compact nonempty
  rw [E.strict_boundary_iff boundary_nonempty]
  constructor
  · intro all_inside
    obtain ⟨p, active⟩ := E.exists_active x
    have inside := all_inside p active
    obtain ⟨member, height⟩ :=
      K.clippedExtension_interior_active_original compact nonempty active inside
    have primal := (K.clippedExtension_active_iff_original compact nonempty member height).mp active
    refine ⟨member, convex_subset_interior_of_avoids_frontier (K.convex_primalNormalCell x)
      compact.isClosed primal.2 inside ?_⟩
    apply Set.disjoint_left.mpr
    intro q normal boundary
    have activeq := (K.clippedExtension_active_iff_original compact nonempty member height).mpr
      ⟨compact.isClosed.frontier_subset boundary, normal⟩
    exact boundary.2 (all_inside q activeq)
  · rintro ⟨member, all_inside⟩
    obtain ⟨p, normal⟩ := K.primalNormalCell_nonempty member
    have height := K.clippedExtension_eq_original_of_normal compact nonempty member normal
      (interior_subset (all_inside normal))
    intro q active
    exact all_inside
      ((K.clippedExtension_active_iff_original compact nonempty member height).mp active).2

end Unfoldings.ConvexRoof
