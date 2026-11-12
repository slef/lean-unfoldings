module

public import Unfoldings.Geometry.PolygonalChain
public import Mathlib.Analysis.Convex.PathConnected

/-! A polygonal chain as an actual continuous path, retaining precisely its closed edge image. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Concatenate the actual closed segments, allowing repeated vertices and flat edges. -/
def path : {n : ℕ} → (P : PolygonalChain E n) → Path (P.vertex 0) (P.vertex (Fin.last n))
  | 0, P => Path.refl (P.vertex 0)
  | n + 1, P =>
    (path (⟨fun j => P.vertex j.castSucc⟩ : PolygonalChain E n)).trans
      (Path.segment (P.vertex (Fin.last n).castSucc) (P.vertex (Fin.last n).succ))

variable {n : ℕ} (P : PolygonalChain E n)

theorem path_range : Set.range P.path = {P.vertex 0} ∪ ⋃ i : Fin n, Set.range (P.point i) := by
  induction n with
  | zero =>
    simp only [path, Path.refl_range, Set.iUnion_of_empty, Set.union_empty]
  | succ n ih =>
    let Q : PolygonalChain E n := ⟨fun j => P.vertex j.castSucc⟩
    have recursive : P.path = Q.path.trans
        (Path.segment (P.vertex (Fin.last n).castSucc) (P.vertex (Fin.last n).succ)) :=
      rfl
    rw [recursive]
    change Set.range (Q.path.trans
      (Path.segment (P.vertex (Fin.last n).castSucc) (P.vertex (Fin.last n).succ))) = _
    rw [Path.trans_range]
    change Set.range Q.path ∪ Set.range (P.point (Fin.last n)) = _
    rw [ih Q]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ((same | ⟨i, s, equal⟩) | ⟨s, equal⟩)
      · exact Or.inl same
      · exact Or.inr ⟨i.castSucc, s, equal⟩
      · exact Or.inr ⟨Fin.last n, s, equal⟩
    · rintro (same | ⟨i, s, equal⟩)
      · exact Or.inl (Or.inl same)
      · revert equal
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro equal
          exact Or.inr ⟨s, equal⟩
        · intro equal
          exact Or.inl (Or.inr ⟨j, s, equal⟩)

/-- When the chain has an edge, every point of its concatenated continuous path is
an actual closed-edge point. The initial point is retained even if all edges are flat. -/
theorem path_point_covered (positive : 0 < n) (s : unitInterval) :
    ∃ i : Fin n, ∃ r : unitInterval, P.path s = P.point i r := by
  have member := P.path_range.subset (Set.mem_range_self s)
  rcases member with same | edge
  · refine ⟨⟨0, positive⟩, 0, ?_⟩
    rw [P.point_zero]
    exact Set.mem_singleton_iff.mp same
  · obtain ⟨i, r, equal⟩ := Set.mem_iUnion.mp edge
    exact ⟨i, r, equal.symm⟩

end Unfoldings.PolygonalChain
