module

public import Unfoldings.Geometry.CompactHalfTurnClosure
public import Unfoldings.Geometry.AcuteChainClosure

/-! A generic apex preserves an open feasible region while avoiding old vertices and edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)
  {I J : Type*} [Finite I] [Finite J]

/-- Given trimmed endpoints away from the old mesh vertices, both supporting
lines of the closure can avoid every old vertex, and its apex can avoid every
old edge. The apex is chosen in any prescribed nonempty open feasible set. -/
theorem exists_regular_twoLink_apex (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) {U : Set Plane} (opens : IsOpen U) (nonempty : U.Nonempty)
    (first : ∀ i, P.vertex 0 ≠ point i) (last : ∀ i, P.vertex (Fin.last n) ≠ point i) :
    ∃ c ∈ U, (∀ j, edge j c ≠ 0) ∧
      ∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let equation : J ⊕ (I ⊕ I) → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim edge (Sum.elim (segmentEquation a ∘ point) (segmentEquation b ∘ point))
  have nonzero : ∀ j, equation j ≠ 0 :=
    Sum.rec proper (Sum.rec (fun _ => segmentEquation_ne_zero _ _)
      (fun _ => segmentEquation_ne_zero _ _))
  obtain ⟨c, c_in, regular⟩ :=
    (AffineArrangement.dense_regular equation nonzero).inter_open_nonempty U opens nonempty
  refine ⟨c, c_in, (fun j => regular (.inl j)), ?_⟩
  intro j t i
  fin_cases j
  · change AffineMap.lineMap b c t ≠ point i
    intro at_vertex
    exact last i (eq_endpoint_of_lineMap_of_segmentEquation_ne_zero
      (regular (.inr (.inr i))) t at_vertex).symm
  · change AffineMap.lineMap c a t ≠ point i
    intro at_vertex
    rw [← AffineMap.lineMap_apply_one_sub] at at_vertex
    exact first i (eq_endpoint_of_lineMap_of_segmentEquation_ne_zero
      (regular (.inr (.inl i))) (1 - t) at_vertex).symm

/-- The strict support constraints leave an open choice for the apex. -/
theorem twoLink_apex_region_open_nonempty (h k : Plane →L[ℝ] ℝ)
    (independent : Function.Surjective fun z => (h z, k z)) :
    IsOpen {c | h c < h (P.vertex 0) ∧ k (P.vertex (Fin.last n)) < k c} ∧
      {c | h c < h (P.vertex 0) ∧ k (P.vertex (Fin.last n)) < k c}.Nonempty := by
  refine ⟨(isOpen_lt h.continuous continuous_const).inter
    (isOpen_lt continuous_const k.continuous), ?_⟩
  obtain ⟨c, equal⟩ := independent (h (P.vertex 0) - 1, k (P.vertex (Fin.last n)) + 1)
  have first := congrArg Prod.fst equal
  have last := congrArg Prod.snd equal
  refine ⟨c, ?_⟩
  change h c < h (P.vertex 0) ∧ k (P.vertex (Fin.last n)) < k c
  constructor <;> linarith only [first, last]

end Unfoldings.PolygonalChain
