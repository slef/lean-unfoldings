module

public import Unfoldings.Topology.CompactJordanDisk

/-! A compact planar Jordan domain can be straightened by an ambient homeomorphism. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- A homeomorphism of the entire plane sends a compact Jordan domain to the closed unit disk. -/
theorem exists_ambientDiskHomeomorph {S : Set Plane} (compact : IsCompact S)
    (nonempty : (interior S).Nonempty) (jordan : Schoenflies.IsJordanCurve (frontier S)) :
    ∃ F : Plane ≃ₜ Plane, F '' S = Metric.closedBall (0 : Plane) 1 := by
  obtain ⟨boundary_map⟩ := jordan.homeomorph isJordanCurve_unitSphere
  obtain ⟨F, agrees⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    jordan isJordanCurve_unitSphere boundary_map
  have boundary_image : F '' frontier S = Metric.sphere (0 : Plane) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [agrees ⟨x, hx⟩]
      exact (boundary_map ⟨x, hx⟩).property
    · intro hy
      let x := boundary_map.symm ⟨y, hy⟩
      refine ⟨x.val, x.property, ?_⟩
      rw [agrees x]
      exact congrArg Subtype.val (boundary_map.apply_symm_apply ⟨y, hy⟩)
  have mapped_boundary : frontier (F '' S) = Metric.sphere (0 : Plane) 1 := by
    rw [← F.image_frontier, boundary_image]
  have mapped_nonempty : (interior (F '' S)).Nonempty := by
    rw [← F.image_interior]
    exact nonempty.image F
  exact ⟨F, compact_eq_closedBall_of_frontier_unitSphere
    (compact.image F.continuous) mapped_nonempty mapped_boundary⟩

end Unfoldings.PlanarTopology
