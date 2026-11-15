module

public import Unfoldings.Geometry.ChainPaths

/-! Recover actual chain vertices from path points that avoid every open edge. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Every path point outside all open edges is one of the original named vertices. -/
theorem exists_vertex_of_mem_path_of_not_open (P : PolygonalChain E n) (x : E)
    (member : x ∈ Set.range P.path)
    (not_open : ∀ i : Fin n, x ∉ openSegment ℝ (P.vertex i.castSucc) (P.vertex i.succ)) :
    ∃ i, P.vertex i = x := by
  rcases P.path_range.subset member with first | pieces
  · exact ⟨0, (Set.mem_singleton_iff.mp first).symm⟩
  obtain ⟨i, t, equal⟩ := Set.mem_iUnion.mp pieces
  by_cases zero : t.val = 0
  · exact ⟨i.castSucc, by simpa only [point, zero, AffineMap.lineMap_apply_zero] using equal⟩
  by_cases one : t.val = 1
  · exact ⟨i.succ, by simpa only [point, one, AffineMap.lineMap_apply_one] using equal⟩
  exact (not_open i ((openSegment_eq_image_lineMap ℝ (P.vertex i.castSucc) (P.vertex i.succ)).symm ▸
    ⟨t.val, ⟨lt_of_le_of_ne t.property.1 (Ne.symm zero),
      lt_of_le_of_ne t.property.2 one⟩, equal⟩)).elim

/-- Removing the two endpoints leaves exactly the original internal vertex indices. -/
theorem exists_internal_vertex_of_mem_path_of_not_open (P : PolygonalChain E (n + 1)) (x : E)
    (member : x ∈ Set.range P.path) (not_first : x ≠ P.vertex 0)
    (not_last : x ≠ P.vertex (Fin.last (n + 1)))
    (not_open : ∀ i : Fin (n + 1), x ∉
      openSegment ℝ (P.vertex i.castSucc) (P.vertex i.succ)) :
    ∃ k : Fin n, P.vertex k.succ.castSucc = x := by
  obtain ⟨i, at_i⟩ := P.exists_vertex_of_mem_path_of_not_open x member not_open
  have positive : 0 < i.val := by
    by_contra nonpositive
    have zero : i = 0 := Fin.ext (by change i.val = 0; omega)
    exact not_first (zero ▸ at_i.symm)
  have before : i.val < n + 1 := by
    by_contra late
    have last : i = Fin.last (n + 1) := Fin.ext (by
      change i.val = n + 1
      have bound := i.isLt
      omega)
    exact not_last (last ▸ at_i.symm)
  let k : Fin n := ⟨i.val - 1, by omega⟩
  refine ⟨k, ?_⟩
  rw [show k.succ.castSucc = i from Fin.ext (by dsimp [k]; omega)]
  exact at_i

end Unfoldings.PolygonalChain
