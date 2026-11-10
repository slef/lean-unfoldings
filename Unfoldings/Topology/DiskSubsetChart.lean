module

public import Unfoldings.Topology.BallBoundaryQuotient

/-! Complements avoiding the boundary of a closed ball have open Euclidean models. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

omit [NormedSpace ℝ E] in
theorem exists_openEmbedding_disk_compl
    (h : X ≃ₜ Metric.closedBall (0 : E) 1) {K : Set X} (closed : IsClosed K)
    (boundary : ∀ x, ‖(h x).val‖ = 1 → x ∈ K) :
    ∃ i : ↥(Kᶜ) → E, Topology.IsOpenEmbedding i := by
  let f : ↥(Kᶜ) → Metric.closedBall (0 : E) 1 := fun z => h z.val
  have ambient_embedding : Topology.IsOpenEmbedding f :=
    h.isOpenEmbedding.comp closed.isOpen_compl.isOpenEmbedding_subtypeVal
  have avoids (z : ↥(Kᶜ)) : f z ∈ (closedBallBoundary (E := E))ᶜ := by
    exact fun equal => z.property (boundary z.val equal)
  let g : ↥(Kᶜ) → ↥((closedBallBoundary (E := E))ᶜ) := fun z => ⟨f z, avoids z⟩
  have embedded : Topology.IsEmbedding g :=
    ambient_embedding.isEmbedding.codRestrict _ avoids
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
  exact ⟨Subtype.val ∘ closedBallInteriorHomeomorph ∘ g,
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp
      (closedBallInteriorHomeomorph.isOpenEmbedding.comp ⟨embedded, open_range⟩)⟩

end Unfoldings
