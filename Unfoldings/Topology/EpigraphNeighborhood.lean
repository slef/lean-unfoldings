module

public import Unfoldings.Topology.TwoGraphJordan
public import Unfoldings.Geometry.PuncturedConvex

/-! At a graph point, local epigraphs have connected punctured neighborhoods. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

open Filter Topology

/-- Subtracting the graph height gives an ambient straightening of the entire epigraph. -/
def graphShear (f : ℝ → ℝ) (hf : Continuous f) : Plane ≃ₜ Plane where
  toFun z := WithLp.toLp 2 ![z 0, z 1 - f (z 0)]
  invFun z := WithLp.toLp 2 ![z 0, z 1 + f (z 0)]
  left_inv z := by
    ext i
    fin_cases i
    · rfl
    · exact sub_add_cancel (z 1) (f (z 0))
  right_inv z := by
    ext i
    fin_cases i
    · rfl
    · exact add_sub_cancel_right (z 1) (f (z 0))
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous.sub
        (hf.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous)
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous.add
        (hf.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous)

theorem graphShear_mem_halfPlane_iff (f : ℝ → ℝ) (hf : Continuous f) (z : Plane) :
    0 ≤ (graphShear f hf z) 1 ↔ f (z 0) ≤ z 1 :=
  sub_nonneg

set_option maxHeartbeats 900000 in
/-- A local ambient convex model gives connected punctured neighborhoods. -/
theorem exists_punctured_neighborhood_of_local_convex_model
    (h : Plane ≃ₜ Plane) {S T : Set Plane} (convex : Convex ℝ T)
    (full : (interior T).Nonempty) {p : Plane} (member : h p ∈ T)
    (near : ∀ᶠ z in 𝓝 p, z ∈ S ↔ h z ∈ T) {r : ℝ} (r_pos : 0 < r) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ Metric.ball p r ∧
      IsPreconnected ((S ∩ N) \ {p}) := by
  obtain ⟨η, η_pos, agrees⟩ := Metric.eventually_nhds_iff_ball.mp near
  let openSet := Metric.ball p r ∩ Metric.ball p η
  have in_image : h p ∈ h '' openSet :=
    ⟨p, ⟨Metric.mem_ball_self r_pos, Metric.mem_ball_self η_pos⟩, rfl⟩
  obtain ⟨ε, ε_pos, fits⟩ := Metric.isOpen_iff.mp
    (h.isOpenMap _ (Metric.isOpen_ball.inter Metric.isOpen_ball)) (h p) in_image
  let N := h ⁻¹' Metric.ball (h p) ε
  have small : N ⊆ openSet := by
    intro q hq
    obtain ⟨z, hz, equal⟩ := fits hq
    exact (h.injective equal) ▸ hz
  let B := T ∩ Metric.ball (h p) ε
  have in_closure : h p ∈ closure (interior T) := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
    exact subset_closure member
  obtain ⟨y, hy, close⟩ := Metric.mem_closure_iff.mp in_closure ε ε_pos
  have full_B : (interior B).Nonempty := by
    rw [show B = T ∩ Metric.ball (h p) ε from rfl, interior_inter,
      Metric.isOpen_ball.interior_eq]
    exact ⟨y, hy, Metric.mem_ball.mpr ((dist_comm y (h p)).trans_lt close)⟩
  have connected : IsPreconnected (B \ {h p}) :=
    (convex_isPathConnected_sdiff_singleton (convex.inter (convex_ball (h p) ε)) full_B
      (h p)).isConnected.isPreconnected
  have image_back : h.symm '' (B \ {h p}) = (S ∩ N) \ {p} := by
    rw [h.symm.image_eq_preimage_symm, Homeomorph.symm_symm]
    ext q
    change ((h q ∈ T ∧ q ∈ N) ∧ h q ≠ h p) ↔ ((q ∈ S ∧ q ∈ N) ∧ q ≠ p)
    constructor
    · rintro ⟨⟨in_T, close⟩, different⟩
      exact ⟨⟨(agrees q (small close).2).mpr in_T, close⟩, fun eq => different (congrArg h eq)⟩
    · rintro ⟨⟨in_S, close⟩, different⟩
      exact ⟨⟨(agrees q (small close).2).mp in_S, close⟩, fun eq => different (h.injective eq)⟩
  have N_open : IsOpen N :=
    (show IsOpen (Metric.ball (h p) ε) from Metric.isOpen_ball).preimage h.continuous
  have center : p ∈ N := show h p ∈ Metric.ball (h p) ε from Metric.mem_ball_self ε_pos
  have included : N ⊆ Metric.ball p r := fun _ hq => (small hq).1
  have related : IsPreconnected ((S ∩ N) \ {p}) := by
    rw [← image_back]
    exact connected.image h.symm h.symm.continuous.continuousOn
  exact ⟨N, N_open, center, included, related⟩

/-- A triangle union that is locally one side of a continuous graph
has only one branch at each point of that graph. -/
theorem exists_punctured_epigraph_neighborhood {f : ℝ → ℝ} (hf : Continuous f)
    {S : Set Plane} {p : Plane} (on_graph : p 1 = f (p 0))
    (near : ∀ᶠ z in 𝓝 p, z ∈ S ↔ f (z 0) ≤ z 1)
    {r : ℝ} (positive : 0 < r) :
    ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ Metric.ball p r ∧
      IsPreconnected ((S ∩ N) \ {p}) := by
  let T := {y : Plane | 0 ≤ y 1}
  have convex : Convex ℝ T := by
    intro x hx y hy a b ha hb _
    change 0 ≤ a * x 1 + b * y 1
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have full : (interior T).Nonempty := by
    let U := {y : Plane | 0 < y 1}
    have open_U : IsOpen U :=
      isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous
    have included : U ⊆ T := fun _ h => (show (0 : ℝ) < _ from h).le
    exact ⟨WithLp.toLp 2 ![0, 1], open_U.subset_interior_iff.mpr included Real.zero_lt_one⟩
  apply exists_punctured_neighborhood_of_local_convex_model (graphShear f hf) convex full
    ((graphShear_mem_halfPlane_iff f hf p).mpr on_graph.ge) _ positive
  filter_upwards [near] with z hz
  exact hz.trans (graphShear_mem_halfPlane_iff f hf z).symm

end Unfoldings.PlanarTopology
