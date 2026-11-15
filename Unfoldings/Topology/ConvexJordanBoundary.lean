module

public import Unfoldings.Topology.PlanarOpenMapping
public import Mathlib.Analysis.Convex.GaugeRescale

/-! A bounded convex planar body has an actual Jordan frontier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

theorem isJordanCurve_frontier_of_convex {S : Set Plane} (convex : Convex ℝ S)
    (inside : (interior S).Nonempty) (bounded : Bornology.IsBounded S) :
    Schoenflies.IsJordanCurve (frontier S) := by
  obtain ⟨h, _, _, boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex inside bounded
  let f : C(Metric.sphere (0 : Plane) 1, Plane) :=
    ⟨fun z => h.symm z.val, h.symm.continuous.comp continuous_subtype_val⟩
  have image : Set.range f = frontier S := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, member, equal⟩ := boundary.symm.subset z.property
      change h.symm z.val ∈ frontier S
      rw [← equal, h.symm_apply_apply]
      exact member
    · intro member
      exact ⟨⟨h p, boundary.subset ⟨p, member, rfl⟩⟩, h.symm_apply_apply p⟩
  rw [← image]
  exact isJordanCurve_range_of_sphere_embedding f (h.symm.injective.comp Subtype.val_injective)

end Unfoldings.PlanarTopology
