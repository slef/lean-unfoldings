module

public import Unfoldings.Source.CompactPaths

/-!
# Stability of a singleton shortest-path fiber

Closed endpoint evaluation from the compact whole path space forces every
shortest path to a nearby endpoint into any prescribed neighborhood of the
unique reference path. Nearby endpoints are not assumed to have unique paths.
-/

@[expose] public section

open scoped Topology

namespace Unfoldings.SourcePath

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X}

theorem endpoint_neighborhood_of_unique (p : SourcePath source)
    (unique : ∀ q : SourcePath source, q.target = p.target → q = p)
    {W : Set (SourcePath source)} (neighborhood : W ∈ 𝓝 p) :
    ∃ V : Set X, V ∈ 𝓝 p.target ∧ ∀ q : SourcePath source, q.target ∈ V → q ∈ W := by
  obtain ⟨S, subset, open_S, at_p⟩ := mem_nhds_iff.mp neighborhood
  let V : Set X := (SourcePath.target '' Sᶜ)ᶜ
  have open_V : IsOpen V := (continuous_target.isClosedMap _ open_S.isClosed_compl).isOpen_compl
  have at_target : p.target ∈ V := by
    rintro ⟨q, outside, equal⟩
    exact outside ((unique q equal).symm ▸ at_p)
  refine ⟨V, open_V.mem_nhds at_target, ?_⟩
  intro q inside
  apply subset
  by_contra outside
  exact inside ⟨q, outside, rfl⟩

end Unfoldings.SourcePath
