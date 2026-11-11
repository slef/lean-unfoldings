module

public import Unfoldings.Geometry.LocalRadialGrowth

/-! Local outward progress on a finite union is witnessed by one fixed piece. -/

@[expose] public section

open Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E]

theorem localRadialGrowth_iff_mem_closure {S : Set E} {q p : E} :
    LocalRadialGrowth S q p ↔ p ∈ closure (S ∩ {x | dist q p < dist q x}) := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro growth ε positive
    obtain ⟨x, member, close, farther⟩ := growth ε positive
    exact ⟨x, ⟨member, farther⟩, dist_comm x p ▸ close⟩
  · intro near ε positive
    obtain ⟨x, ⟨member, farther⟩, close⟩ := near ε positive
    exact ⟨x, member, dist_comm p x ▸ close, farther⟩

/-- Finiteness prevents outward progress from escaping among different pieces as the radius
shrinks. No closedness or local regularity of the individual pieces is needed. -/
theorem LocalRadialGrowth.exists_piece {I : Type*} [Finite I] {S : Set E} {q p : E}
    (growth : LocalRadialGrowth S q p) (piece : I → Set E) (cover : S ⊆ ⋃ i, piece i) :
    ∃ i, LocalRadialGrowth (piece i) q p := by
  have near := localRadialGrowth_iff_mem_closure.mp (growth.mono cover)
  have distribute : (⋃ i, piece i) ∩ {x | dist q p < dist q x} =
      ⋃ i, piece i ∩ {x | dist q p < dist q x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_and_right]
  rw [distribute, closure_iUnion_of_finite] at near
  obtain ⟨i, incident⟩ := Set.mem_iUnion.mp near
  exact ⟨i, localRadialGrowth_iff_mem_closure.mpr incident⟩

end Unfoldings
