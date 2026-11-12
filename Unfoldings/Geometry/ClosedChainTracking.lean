module

public import Unfoldings.Geometry.PolygonalChain

/-! Tracking a finite actual polygonal chain on an open height interval includes both endpoints. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- A finite compact union of actual whole chain edges preserves endpoint tracking. -/
theorem tracked_on_closed_interval {γ : ℝ → E} (continuous : Continuous γ)
    {a b : ℝ} (ordered : a < b)
    (tracked : ∀ h ∈ Set.Ioo a b, ∃ j : Fin n, ∃ s : unitInterval, γ h = P.point j s) :
    ∀ h ∈ Set.Icc a b, ∃ j : Fin n, ∃ s : unitInterval, γ h = P.point j s := by
  let carrier := ⋃ j : Fin n, Set.range (P.point j)
  have closed : IsClosed carrier := isClosed_iUnion_of_finite fun j =>
    (isCompact_range (show Continuous (P.point j) from
      AffineMap.lineMap_continuous.comp continuous_subtype_val)).isClosed
  have inside : Set.Ioo a b ⊆ γ ⁻¹' carrier := by
    intro h member
    obtain ⟨j, s, equal⟩ := tracked h member
    exact Set.mem_iUnion.mpr ⟨j, ⟨s, equal.symm⟩⟩
  intro h member
  have approached : h ∈ closure (Set.Ioo a b) := (closure_Ioo ordered.ne).symm ▸ member
  obtain ⟨j, s, equal⟩ := Set.mem_iUnion.mp
    (closure_minimal inside (closed.preimage continuous) approached)
  exact ⟨j, s, equal.symm⟩

end Unfoldings.PolygonalChain
