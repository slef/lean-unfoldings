module

public import Unfoldings.Topology.PlanarOpenMapping
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact planar sets with Jordan frontier are disks

A compact planar set with nonempty interior and unit-circle frontier is the
closed unit disk. Connectedness separates the open ball and its exterior;
compactness excludes the exterior. Jordan–Schönflies then reduces an arbitrary
Jordan frontier to this model. No surface classification or Euler count enters.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

theorem isConnected_outside_unitBall : IsConnected {x : Plane | 1 < ‖x‖} := by
  have dimension : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have sphere_connected : IsConnected (Metric.sphere (0 : Plane) 1) :=
    isConnected_sphere dimension 0 zero_le_one
  have radii_connected : IsConnected (Set.Ioi (1 : ℝ)) := isConnected_Ioi
  have image : (fun p : Plane × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : Plane) 1 ×ˢ Set.Ioi (1 : ℝ)) = {x : Plane | 1 < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      have norm_u : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      change 1 < ‖r • u‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr), norm_u, mul_one]
      exact hr
    · intro hx
      change 1 < ‖x‖ at hx
      have nonzero : x ≠ 0 := by intro zero; simp only [zero, norm_zero] at hx; linarith
      let u := unitDirection ⟨x, nonzero⟩
      refine ⟨(u.val, ‖x‖), ⟨u.property, hx⟩, ?_⟩
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero), one_smul]
  rw [← image]
  exact (sphere_connected.prod radii_connected).image _
    (continuous_snd.smul continuous_fst).continuousOn

theorem subset_interior_or_compl_of_avoids_frontier {K S : Set Plane} (closed : IsClosed K)
    (connected : IsPreconnected S) (avoids : Disjoint S (frontier K)) :
    S ⊆ interior K ∨ S ⊆ Kᶜ := by
  have disjoint : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr (fun _ inside outside => outside (interior_subset inside))
  have cover : S ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases inside : x ∈ K
    · left
      by_contra outside
      exact Set.disjoint_left.mp avoids hx ((closed.frontier_eq).symm ▸ ⟨inside, outside⟩)
    · exact Or.inr inside
  exact IsPreconnected.subset_or_subset isOpen_interior closed.isOpen_compl disjoint cover connected

theorem compact_eq_closedBall_of_frontier_unitSphere {K : Set Plane} (compact : IsCompact K)
    (nonempty : (interior K).Nonempty) (boundary : frontier K = Metric.sphere (0 : Plane) 1) :
    K = Metric.closedBall (0 : Plane) 1 := by
  have exterior_avoids : Disjoint {x : Plane | 1 < ‖x‖} (frontier K) := by
    rw [boundary]
    apply Set.disjoint_left.mpr
    intro x hx hs
    have norm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
    change 1 < ‖x‖ at hx
    rw [norm] at hx
    exact lt_irrefl 1 hx
  have exterior_alternative := subset_interior_or_compl_of_avoids_frontier compact.isClosed
    isConnected_outside_unitBall.isPreconnected exterior_avoids
  obtain ⟨R, bound⟩ := compact.isBounded.exists_norm_le
  obtain ⟨z, norm_z⟩ := exists_norm_eq Plane (show 0 ≤ max R 1 + 1 by
    linarith [le_max_right R 1])
  have exterior_z : 1 < ‖z‖ := by rw [norm_z]; linarith [le_max_right R 1]
  have absent_z : z ∉ K := by
    intro hz
    have estimate := bound z hz
    rw [norm_z] at estimate
    linarith [le_max_left R 1]
  have exterior_outside : {x : Plane | 1 < ‖x‖} ⊆ Kᶜ := by
    rcases exterior_alternative with included | excluded
    · exact (absent_z (interior_subset (included exterior_z))).elim
    · exact excluded
  have included : K ⊆ Metric.closedBall (0 : Plane) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra outside
    exact exterior_outside (lt_of_not_ge outside) hx
  have interior_avoids : Disjoint (Metric.ball (0 : Plane) 1) (frontier K) := by
    rw [boundary]
    apply Set.disjoint_left.mpr
    intro x hx hs
    have norm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
    have small : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [norm] at small
    exact lt_irrefl 1 small
  have interior_alternative := subset_interior_or_compl_of_avoids_frontier compact.isClosed
    Metric.isPreconnected_ball interior_avoids
  have ball_included : Metric.ball (0 : Plane) 1 ⊆ K := by
    rcases interior_alternative with inner | outer
    · exact fun _ hx => interior_subset (inner hx)
    · obtain ⟨x, hx⟩ := nonempty
      have near := interior_mono included hx
      rw [interior_closedBall (0 : Plane) one_ne_zero] at near
      exact (outer near (interior_subset hx)).elim
  apply Set.Subset.antisymm included
  rw [← closure_ball (0 : Plane) one_ne_zero]
  exact closure_minimal ball_included compact.isClosed

theorem exists_diskHomeomorph_of_compact_Jordan_frontier {K : Set Plane}
    (compact : IsCompact K) (nonempty : (interior K).Nonempty)
    (jordan : Schoenflies.IsJordanCurve (frontier K)) :
    Nonempty (K ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  obtain ⟨boundary_map⟩ := jordan.homeomorph isJordanCurve_unitSphere
  obtain ⟨F, agrees⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    jordan isJordanCurve_unitSphere boundary_map
  have boundary_image : F '' frontier K = Metric.sphere (0 : Plane) 1 := by
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
  have mapped_boundary : frontier (F '' K) = Metric.sphere (0 : Plane) 1 := by
    rw [← F.image_frontier, boundary_image]
  have mapped_nonempty : (interior (F '' K)).Nonempty := by
    rw [← F.image_interior]
    exact nonempty.image F
  have mapped := compact_eq_closedBall_of_frontier_unitSphere
    (compact.image F.continuous) mapped_nonempty mapped_boundary
  exact ⟨(F.image K).trans (Homeomorph.setCongr mapped)⟩

end Unfoldings.PlanarTopology
