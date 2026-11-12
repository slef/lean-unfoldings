module

public import Unfoldings.Geometry.ChainLinear

/-! Exact finite prefixes of polygonal chains, ending partway through an actual edge. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- Retain the vertices through the initial vertex of `i`, and end at its point `s`.
The last edge may be zero; no extension past the chosen point is introduced. -/
def truncate (i : Fin n) (s : unitInterval) : PolygonalChain E (i.val + 1) where
  vertex j := if before : j.val ≤ i.val then P.vertex ⟨j.val, by omega⟩ else P.point i s

theorem truncate_vertex_before (i : Fin n) (s : unitInterval) (j : Fin (n + 1))
    (before : j.val ≤ i.val) :
    (P.truncate i s).vertex ⟨j.val, by omega⟩ = P.vertex j := by
  simp only [truncate, dite_eq_left before]

@[simp] theorem truncate_vertex_last (i : Fin n) (s : unitInterval) :
    (P.truncate i s).vertex (Fin.last (i.val + 1)) = P.point i s := by
  dsimp only [truncate]
  split_ifs with before
  · change i.val + 1 ≤ i.val at before
    omega
  · rfl

theorem truncate_point_before (i : Fin n) (s : unitInterval) (j : Fin (i.val + 1))
    (before : j.val < i.val) (r : unitInterval) :
    (P.truncate i s).point j r = P.point ⟨j.val, by omega⟩ r := by
  have first : (P.truncate i s).vertex j.castSucc =
      P.vertex (⟨j.val, by omega⟩ : Fin n).castSucc :=
    P.truncate_vertex_before i s (⟨j.val, by omega⟩ : Fin (n + 1)) before.le
  have last : (P.truncate i s).vertex j.succ =
      P.vertex (⟨j.val, by omega⟩ : Fin n).succ :=
    P.truncate_vertex_before i s (⟨j.val + 1, by omega⟩ : Fin (n + 1))
      (by change j.val + 1 ≤ i.val; omega)
  change AffineMap.lineMap _ _ (r : ℝ) = AffineMap.lineMap _ _ (r : ℝ)
  rw [first, last]

theorem truncate_point_last (i : Fin n) (s r : unitInterval) :
    (P.truncate i s).point (Fin.last i.val) r =
      AffineMap.lineMap (P.vertex i.castSucc) (P.vertex i.succ) ((s : ℝ) * (r : ℝ)) := by
  have first : (P.truncate i s).vertex (Fin.last i.val).castSucc = P.vertex i.castSucc :=
    P.truncate_vertex_before i s i.castSucc (le_refl i.val)
  have last : (P.truncate i s).vertex (Fin.last i.val).succ = P.point i s :=
    P.truncate_vertex_last i s
  change AffineMap.lineMap _ _ (r : ℝ) = _
  rw [first, last]
  simp only [point, AffineMap.lineMap_apply_module]
  module

/-- Every point of the truncated chain is an actual point before its named endpoint
in the original chain, including a possibly collapsed final edge. -/
theorem truncate_point_covered (i : Fin n) (s : unitInterval)
    (j : Fin (i.val + 1)) (r : unitInterval) :
    ∃ k : Fin n, ∃ u : unitInterval,
      Before k u i s ∧ (P.truncate i s).point j r = P.point k u := by
  by_cases before : j.val < i.val
  · exact ⟨⟨j.val, by omega⟩, r, Or.inl before, P.truncate_point_before i s j before r⟩
  · have last : j = Fin.last i.val := Fin.ext (by change j.val = i.val; omega)
    let u : unitInterval := ⟨(s : ℝ) * (r : ℝ),
      mul_nonneg s.property.1 r.property.1,
      (mul_le_mul_of_nonneg_left r.property.2 s.property.1).trans (by simpa using s.property.2)⟩
    have ordered : u ≤ s := by
      change (s : ℝ) * (r : ℝ) ≤ (s : ℝ)
      nlinarith [s.property.1, r.property.2]
    refine ⟨i, u, Or.inr ⟨rfl, ordered⟩, ?_⟩
    rw [last, P.truncate_point_last]
    rfl

end Unfoldings.PolygonalChain
