module

public import Unfoldings.Geometry.SegmentEndpointGerm
public import Unfoldings.Geometry.SegmentVertices

/-! A ray germ on a finite edge skeleton follows an actual incident edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

theorem exists_incident_segment_of_ray_germ {I : Type*} [Finite I]
    (first last : I → Plane) (p d : Plane)
    (follows : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • d ∈ ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, p ∈ segment ℝ (first i) (last i) ∧
      ∃ k : ℝ, d = k • (last i - first i) := by
  have away : ∀ᶠ x in 𝓝 p, ∀ i, p ∉ segment ℝ (first i) (last i) →
      x ∉ segment ℝ (first i) (last i) := by
    apply (Filter.eventually_all.2 _)
    intro i
    by_cases member : p ∈ segment ℝ (first i) (last i)
    · exact Eventually.of_forall (fun _ h => (h member).elim)
    · have missing : ∀ᶠ x in 𝓝 p, x ∉ segment ℝ (first i) (last i) :=
        (compact_segment (first i) (last i)).isClosed.isOpen_compl.mem_nhds member
      exact missing.mono (fun _ outside _ => outside)
  have continuous_ray : Continuous (fun t : ℝ => p + t • d) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have at_zero : Tendsto (fun t : ℝ => p + t • d) (𝓝[>] 0) (𝓝 p) := by
    have h := continuous_ray.continuousAt (x := 0)
    change Tendsto (fun t : ℝ => p + t • d) (𝓝 0) (𝓝 (p + (0 : ℝ) • d)) at h
    have near := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [zero_smul, add_zero] using near
  have close := at_zero.eventually away
  have positive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, membership, away_at, tp⟩ := (follows.and (close.and positive)).exists
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp membership
  have at_p : p ∈ segment ℝ (first i) (last i) :=
    by_contra (fun absent => away_at i absent on_segment)
  obtain ⟨r, _, hr⟩ := (segment_eq_image_lineMap ℝ (first i) (last i)).le at_p
  obtain ⟨s, _, hs⟩ := (segment_eq_image_lineMap ℝ (first i) (last i)).le on_segment
  rw [AffineMap.lineMap_apply_module'] at hr hs
  have scaled : t • d = (s - r) • (last i - first i) := calc
    _ = (p + t • d) - p := by abel
    _ = (s • (last i - first i) + first i) - (r • (last i - first i) + first i) := by
      rw [← hs, ← hr]
    _ = _ := by module
  refine ⟨i, at_p, (s - r) / t, ?_⟩
  have eq := congrArg (fun x : Plane => t⁻¹ • x) scaled
  simpa only [smul_smul, inv_mul_cancel₀ tp.ne', one_smul, div_eq_inv_mul] using eq

end Unfoldings
