module

public import Unfoldings.Geometry.ChainEndTrimPaths
public import Unfoldings.Geometry.ChainEndTrimTurns
public import Mathlib.Topology.Algebra.Module.Cardinality

/-! Choose actual interior endpoint fractions that avoid any finite prescribed set of vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A genuine segment has interior parameters avoiding all prescribed finite exceptional points. -/
theorem exists_interior_segment_parameter_avoiding {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Finite ι] (a b : E) (different : a ≠ b) (point : ι → E) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      ∀ i, AffineMap.lineMap a b (t : ℝ) ≠ point i := by
  let exceptional : Set ℝ := (AffineMap.lineMap a b) ⁻¹' Set.range point
  have finite : exceptional.Finite :=
    (Set.finite_range point).preimage (AffineMap.lineMap_injective ℝ different).injOn
  obtain ⟨t, outside, inside⟩ := finite.countable.dense_compl ℝ |>.exists_mem_open
    isOpen_Ioo (show (Set.Ioo (0 : ℝ) 1).Nonempty from ⟨1 / 2, by norm_num⟩)
  refine ⟨⟨t, inside.1.le, inside.2.le⟩, inside.1, inside.2, ?_⟩
  intro i same
  exact outside ⟨i, same.symm⟩

namespace PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E (n + 2))

/-- Keep every original turn, moving both endpoints into their original links away from vertices. -/
theorem exists_generic_trimEnds {ι : Type*} [Finite ι] (point : ι → E)
    (first_nonzero : P.edge 0 ≠ 0) (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0) :
    ∃ a b : unitInterval, (0 < (a : ℝ) ∧ (a : ℝ) < 1) ∧
      (0 < (b : ℝ) ∧ (b : ℝ) < 1) ∧
      ∀ i, (P.trimEnds a b).vertex 0 ≠ point i ∧
        (P.trimEnds a b).vertex (Fin.last (n + 2)) ≠ point i := by
  have first : P.vertex (0 : Fin (n + 2)).castSucc ≠ P.vertex (0 : Fin (n + 2)).succ := by
    intro same
    apply first_nonzero
    simp only [edge, same, sub_self]
  have last : P.vertex (Fin.last (n + 1)).castSucc ≠ P.vertex (Fin.last (n + 1)).succ := by
    intro same
    apply last_nonzero
    simp only [edge, same, sub_self]
  obtain ⟨a, first_pos, first_small, first_regular⟩ :=
    exists_interior_segment_parameter_avoiding _ _ first point
  obtain ⟨b, last_pos, last_small, last_regular⟩ :=
    exists_interior_segment_parameter_avoiding _ _ last point
  exact ⟨a, b, ⟨first_pos, first_small⟩, ⟨last_pos, last_small⟩, fun i => by
    rw [P.trimEnds_start, P.trimEnds_last]
    exact ⟨first_regular i, last_regular i⟩⟩

end PolygonalChain
end Unfoldings
