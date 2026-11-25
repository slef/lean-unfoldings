module

public import Unfoldings.Geometry.AcuteChainEndpointRays

/-! For two forward chains, their local endpoint rays are those of their first and last links. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n m : ℕ} (P : PolygonalChain Plane (n + 1)) (Q : PolygonalChain Plane (m + 1))
  (h : Plane →L[ℝ] ℝ) (p_progress : ∀ i, 0 < h (P.edge i)) (q_progress : ∀ i, 0 < h (Q.edge i))

include p_progress q_progress in
/-- Near their common starting point two forward chains each have just one ray. -/
theorem eventually_mem_union_forwardChains_iff_initial_rays (same : Q.vertex 0 = P.vertex 0) :
    ∀ᶠ z in 𝓝 (P.vertex 0), z ∈ Set.range P.path ∪ Set.range Q.path ↔
      z - P.vertex 0 ∈ nonnegativeRay (P.edge 0) ∪ nonnegativeRay (Q.edge 0) := by
  have q_near := Q.eventually_mem_linear_path_iff_initial_ray h q_progress
  simp only [same] at q_near
  filter_upwards [P.eventually_mem_linear_path_iff_initial_ray h p_progress, q_near]
    with z hp hq
  exact or_congr hp hq

include p_progress q_progress in
/-- Near their common final point two forward chains each have just one reverse ray. -/
theorem eventually_mem_union_forwardChains_iff_terminal_rays
    (same : Q.vertex (Fin.last (m + 1)) = P.vertex (Fin.last (n + 1))) :
    let b := P.vertex (Fin.last (n + 1))
    ∀ᶠ z in 𝓝 b, z ∈ Set.range P.path ∪ Set.range Q.path ↔
      z - b ∈ nonnegativeRay (-P.edge (Fin.last n)) ∪ nonnegativeRay (-Q.edge (Fin.last m)) := by
  have q_near := Q.eventually_mem_linear_path_iff_terminal_ray h q_progress
  dsimp only at q_near ⊢
  simp only [same] at q_near
  filter_upwards [P.eventually_mem_linear_path_iff_terminal_ray h p_progress, q_near]
    with z hp hq
  exact or_congr hp hq

end Unfoldings.PolygonalChain
