module

public import Unfoldings.Geometry.CompactTwoLinkClosure

/-! Align and mark the actual two-link closures using the common polygonal completion API. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

theorem threeSegmentClosure_of_initial_eq_twoLinkClosure (c : Plane) :
    P.threeSegmentClosure (P.vertex 0) c = P.twoLinkClosure c := by
  ext p
  have first : p ∈ segment ℝ (P.vertex 0) (P.vertex 0) → p ∈ Set.range P.path := by
    rw [segment_same, Set.mem_singleton_iff]
    intro eq
    exact eq ▸ P.vertex_mem_path_range 0
  constructor
  · rintro (trace | (last | initial) | at_start)
    · exact Or.inl trace
    · exact Or.inr (Or.inl last)
    · exact Or.inr (Or.inr initial)
    · exact Or.inl (first at_start)
  · rintro (trace | last | initial)
    · exact Or.inl trace
    · exact Or.inr (Or.inl (Or.inl last))
    · exact Or.inr (Or.inl (Or.inr initial))

theorem twoLinkClosure_subset_of_convex {c : Plane} {region : Set Plane}
    (convex : Convex ℝ region) (trace : Set.range P.path ⊆ region) (apex : c ∈ region) :
    P.twoLinkClosure c ⊆ region := by
  rintro p (on_bank | at_end | at_start)
  · exact trace on_bank
  · exact convex.segment_subset (trace (P.vertex_mem_path_range _)) apex at_end
  · exact convex.segment_subset apex (trace (P.vertex_mem_path_range _)) at_start

/-- On a common convex comparison region choose a regular connector for one
bank side, with the full loop interior to that region. -/
theorem exists_regular_twoLink_closure_in_region (h k : Plane →L[ℝ] ℝ)
    (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i)) (nonempty : 0 < n)
    {region : Set Plane} (convex : Convex ℝ region) (trace : Set.range P.path ⊆ interior region)
    (feasible : {c | c ∈ interior region ∧ h c < h (P.vertex 0) ∧
      k (P.vertex (Fin.last n)) < k c}.Nonempty)
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (start : ∀ i, P.vertex 0 ≠ point i)
    (finish : ∀ i, P.vertex (Fin.last n) ≠ point i) :
    ∃ c, h c < h (P.vertex 0) ∧ k (P.vertex (Fin.last n)) < k c ∧
      P.twoLinkClosure c ⊆ interior region ∧ Schoenflies.IsJordanCurve (P.twoLinkClosure c) ∧
      (∀ j, edge j c ≠ 0) ∧
      ∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i := by
  have opens : IsOpen {c | c ∈ interior region ∧ h c < h (P.vertex 0) ∧
      k (P.vertex (Fin.last n)) < k c} :=
    isOpen_interior.inter ((isOpen_lt h.continuous continuous_const).inter
      (isOpen_lt continuous_const k.continuous))
  obtain ⟨c, ⟨inside, initial, terminal⟩, regular, links⟩ :=
    P.exists_regular_twoLink_apex point edge proper opens feasible start finish
  exact ⟨c, initial, terminal, P.twoLinkClosure_subset_of_convex convex.interior trace inside,
    P.isJordanCurve_twoLinkClosure c h k first last initial.le terminal.le nonempty, regular, links⟩

theorem trimEnds_positive_linear_edges (Q : PolygonalChain Plane (n + 2))
    (a b : unitInterval) (first : a.val < 1) (last : 0 < b.val)
    (h : Plane →L[ℝ] ℝ) (progress : ∀ i, 0 < h (Q.edge i)) :
    ∀ i, 0 < h ((Q.trimEnds a b).edge i) := by
  intro i
  rw [Q.trimEnds_edge, map_smul, smul_eq_mul]
  apply mul_pos _ (progress i)
  split_ifs <;> linarith only [first, last]

end Unfoldings.PolygonalChain
