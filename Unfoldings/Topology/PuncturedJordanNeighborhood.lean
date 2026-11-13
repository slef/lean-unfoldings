module

public import Unfoldings.Topology.AmbientJordanDisk
public import Unfoldings.Geometry.PuncturedConvex

/-! Jordan disks admit arbitrarily small connected punctured relative neighborhoods. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- Straightening a Jordan disk constructs connected punctured neighborhoods at both its
interior and boundary points. The neighborhood is open in the ambient plane. -/
theorem exists_punctured_connected_neighborhood {S : Set Plane} (h : Plane ≃ₜ Plane)
    (image : h '' S = Metric.closedBall (0 : Plane) 1) {p : Plane} (member : p ∈ S)
    {r : ℝ} (positive : 0 < r) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ Metric.ball p r ∧
      IsPreconnected ((S ∩ N) \ {p}) := by
  have inside_image : h p ∈ h '' Metric.ball p r :=
    ⟨p, Metric.mem_ball_self positive, rfl⟩
  obtain ⟨ε, εpos, ball_inside⟩ := Metric.isOpen_iff.mp
    (h.isOpenMap _ Metric.isOpen_ball) _ inside_image
  let N := h ⁻¹' Metric.ball (h p) ε
  let B := Metric.closedBall (0 : Plane) 1 ∩ Metric.ball (h p) ε
  have member_disk : h p ∈ Metric.closedBall (0 : Plane) 1 := image ▸ ⟨p, member, rfl⟩
  have in_closure : h p ∈ closure (Metric.ball (0 : Plane) 1) := by
    rw [closure_ball (0 : Plane) one_ne_zero]
    exact member_disk
  obtain ⟨z, in_ball, close⟩ := Metric.mem_closure_iff.mp in_closure ε εpos
  have full : (interior B).Nonempty := by
    have open_patch : IsOpen (Metric.ball (0 : Plane) 1 ∩ Metric.ball (h p) ε) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have included : Metric.ball (0 : Plane) 1 ∩ Metric.ball (h p) ε ⊆ B :=
      Set.inter_subset_inter_left _ Metric.ball_subset_closedBall
    exact ⟨z, open_patch.subset_interior_iff.mpr included
      ⟨in_ball, by simpa only [Metric.mem_ball, dist_comm] using close⟩⟩
  have connected : IsPreconnected (B \ {h p}) :=
    (convex_isPathConnected_sdiff_singleton
      ((convex_closedBall (0 : Plane) 1).inter (convex_ball (h p) ε)) full
      (h p)).isConnected.isPreconnected
  have image_back : h.symm '' (B \ {h p}) = (S ∩ N) \ {p} := by
    ext q
    constructor
    · rintro ⟨w, ⟨⟨in_disk, near⟩, different⟩, rfl⟩
      have in_image : w ∈ h '' S := image.symm ▸ in_disk
      obtain ⟨a, ha, equal⟩ := in_image
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [← equal, h.symm_apply_apply] using ha
      · change h (h.symm w) ∈ Metric.ball (h p) ε
        simpa only [h.apply_symm_apply] using near
      · intro equal_p
        apply different
        exact Set.mem_singleton_iff.mpr ((h.apply_symm_apply w).symm.trans (congrArg h equal_p))
    · rintro ⟨⟨in_S, near⟩, different⟩
      refine ⟨h q, ⟨⟨?_, near⟩, ?_⟩, h.symm_apply_apply q⟩
      · rw [← image]
        exact ⟨q, in_S, rfl⟩
      · exact fun equal => different (h.injective equal)
  have open_N : IsOpen N :=
    (show IsOpen (Metric.ball (h p) ε) from Metric.isOpen_ball).preimage h.continuous
  have point_N : p ∈ N := by
    change dist (h p) (h p) < ε
    simpa only [dist_self] using εpos
  refine ⟨N, open_N, point_N, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, ha, equal⟩ := ball_inside hq
    exact h.injective equal ▸ ha
  · rw [← image_back]
    exact connected.image _ h.symm.continuous.continuousOn

end Unfoldings.PlanarTopology
