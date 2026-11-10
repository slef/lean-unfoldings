module

public import Unfoldings.Topology.SphereChart

/-! Complements of nonempty closed sets in a sphere admit open Euclidean embeddings. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem exists_openEmbedding_sphere_compl (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (h : X ≃ₜ Metric.sphere (0 : E) 1) {K : Set X} (closed : IsClosed K) (nonempty : K.Nonempty) :
    ∃ i : ↥(Kᶜ) → EuclideanSpace ℝ (Fin n), Topology.IsOpenEmbedding i := by
  obtain ⟨pole, pole_mem⟩ := nonempty
  let spherePole := h pole
  let puncture := ({spherePole} : Set (Metric.sphere (0 : E) 1))ᶜ
  let f : ↥(Kᶜ) → Metric.sphere (0 : E) 1 := fun z => h z.val
  have ambient_embedding : Topology.IsOpenEmbedding f :=
    h.isOpenEmbedding.comp closed.isOpen_compl.isOpenEmbedding_subtypeVal
  have avoids (z : ↥(Kᶜ)) : f z ∈ puncture := by
    change h z.val ≠ spherePole
    intro same
    exact z.property ((h.injective same).symm ▸ pole_mem)
  let g : ↥(Kᶜ) → puncture := fun z => ⟨f z, avoids z⟩
  have embedded : Topology.IsEmbedding g :=
    ambient_embedding.isEmbedding.codRestrict puncture avoids
  have range_eq : Set.range g = Subtype.val ⁻¹' Set.range f := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, equal⟩
      exact ⟨x, Subtype.ext equal⟩
  have open_range : IsOpen (Set.range g) := by
    rw [range_eq]
    exact ambient_embedding.isOpen_range.preimage continuous_subtype_val
  let chart := spherePunctureHomeomorph n spherePole
  exact ⟨chart ∘ g, chart.isOpenEmbedding.comp ⟨embedded, open_range⟩⟩

end Unfoldings
