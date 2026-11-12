module

public import Unfoldings.Geometry.ChainLinear

/-! Join a finite family of directed segments by explicit straight gap segments. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} {n : ℕ}

/-- Start at `origin`, jump to the first segment, traverse it, then alternate gap and
original segments. Repeated endpoints and zero gap segments are retained. -/
def interleavedSegments (origin : E) (first last : Fin n → E) : PolygonalChain E (2 * n) where
  vertex k :=
    if zero : k.val = 0 then origin
    else if odd : k.val % 2 = 1 then first ⟨k.val / 2, by omega⟩
    else last ⟨k.val / 2 - 1, by omega⟩

variable (origin : E) (first last : Fin n → E)

/-- The preceding original segment's endpoint, or the common origin for the initial gap. -/
def segmentPredecessor (j : Fin n) : E :=
  if zero : j.val = 0 then origin else last ⟨j.val - 1, by omega⟩

@[simp] theorem interleavedSegments_vertex_zero :
    (interleavedSegments origin first last).vertex 0 = origin := rfl

theorem interleavedSegments_vertex_first (j : Fin n) :
    (interleavedSegments origin first last).vertex ⟨2 * j.val + 1, by omega⟩ = first j := by
  have nonzero : 2 * j.val + 1 ≠ 0 := by omega
  have odd : (2 * j.val + 1) % 2 = 1 := by omega
  simp only [interleavedSegments, dite_eq_right nonzero, dite_eq_left odd]
  congr 1
  apply Fin.ext
  change (2 * j.val + 1) / 2 = j.val
  omega

theorem interleavedSegments_vertex_last (j : Fin n) :
    (interleavedSegments origin first last).vertex ⟨2 * (j.val + 1), by omega⟩ = last j := by
  have nonzero : 2 * (j.val + 1) ≠ 0 := by omega
  have even : (2 * (j.val + 1)) % 2 ≠ 1 := by omega
  simp only [interleavedSegments, dite_eq_right nonzero, dite_eq_right even]
  congr 1
  apply Fin.ext
  change 2 * (j.val + 1) / 2 - 1 = j.val
  omega

theorem interleavedSegments_vertex_predecessor (j : Fin n) :
    (interleavedSegments origin first last).vertex ⟨2 * j.val, by omega⟩ =
      segmentPredecessor origin last j := by
  by_cases zero : j.val = 0
  · have index : (⟨2 * j.val, by omega⟩ : Fin (2 * n + 1)) = 0 :=
      Fin.ext (by change 2 * j.val = 0; omega)
    rw [index, interleavedSegments_vertex_zero]
    simp only [segmentPredecessor, dite_eq_left zero]
  · let previous : Fin n := ⟨j.val - 1, by omega⟩
    have index : (⟨2 * j.val, by omega⟩ : Fin (2 * n + 1)) =
        ⟨2 * (previous.val + 1), by dsimp only [previous]; omega⟩ :=
      Fin.ext (by change 2 * j.val = 2 * (j.val - 1 + 1); omega)
    rw [index, interleavedSegments_vertex_last]
    simp only [segmentPredecessor, dite_eq_right zero, previous]

variable [NormedAddCommGroup E]

theorem interleavedSegments_original_edge (j : Fin n) :
    (interleavedSegments origin first last).edge ⟨2 * j.val + 1, by omega⟩ = last j - first j := by
  let k : Fin (2 * n) := ⟨2 * j.val + 1, by omega⟩
  have before : k.castSucc = (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n + 1)) := rfl
  have after : k.succ = (⟨2 * (j.val + 1), by omega⟩ : Fin (2 * n + 1)) :=
    Fin.ext (by change 2 * j.val + 1 + 1 = 2 * (j.val + 1); omega)
  change (interleavedSegments origin first last).edge k = _
  rw [edge, before, after, interleavedSegments_vertex_first, interleavedSegments_vertex_last]

theorem interleavedSegments_gap_edge (j : Fin n) :
    (interleavedSegments origin first last).edge ⟨2 * j.val, by omega⟩ =
      first j - segmentPredecessor origin last j := by
  let k : Fin (2 * n) := ⟨2 * j.val, by omega⟩
  have before : k.castSucc = (⟨2 * j.val, by omega⟩ : Fin (2 * n + 1)) := rfl
  have after : k.succ = (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n + 1)) := rfl
  change (interleavedSegments origin first last).edge k = _
  rw [edge, before, after, interleavedSegments_vertex_predecessor,
    interleavedSegments_vertex_first]

/-- Prove a property of every edge by checking the actual segments and the explicit gaps. -/
theorem interleavedSegments_edges {property : E → Prop}
    (gaps : ∀ j, property (first j - segmentPredecessor origin last j))
    (originals : ∀ j, property (last j - first j)) (k : Fin (2 * n)) :
    property ((interleavedSegments origin first last).edge k) := by
  let j : Fin n := ⟨k.val / 2, by omega⟩
  by_cases even : k.val % 2 = 0
  · have index : k = ⟨2 * j.val, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2); omega)
    rw [index, interleavedSegments_gap_edge]
    exact gaps j
  · have index : k = ⟨2 * j.val + 1, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2) + 1; omega)
    rw [index, interleavedSegments_original_edge]
    exact originals j

/-- Matched edges of two interleavings satisfy a relation when each matched gap and
each matched original segment does. -/
theorem interleavedSegments_paired_edges (otherOrigin : E) (otherFirst otherLast : Fin n → E)
    {relation : E → E → Prop}
    (gaps : ∀ j, relation (first j - segmentPredecessor origin last j)
      (otherFirst j - segmentPredecessor otherOrigin otherLast j))
    (originals : ∀ j, relation (last j - first j) (otherLast j - otherFirst j))
    (k : Fin (2 * n)) :
    relation ((interleavedSegments origin first last).edge k)
      ((interleavedSegments otherOrigin otherFirst otherLast).edge k) := by
  let j : Fin n := ⟨k.val / 2, by omega⟩
  by_cases even : k.val % 2 = 0
  · have index : k = ⟨2 * j.val, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2); omega)
    rw [index, interleavedSegments_gap_edge, interleavedSegments_gap_edge]
    exact gaps j
  · have index : k = ⟨2 * j.val + 1, by dsimp only [j]; omega⟩ :=
      Fin.ext (by change k.val = 2 * (k.val / 2) + 1; omega)
    rw [index, interleavedSegments_original_edge, interleavedSegments_original_edge]
    exact originals j

variable [InnerProductSpace ℝ E]

theorem interleavedSegments_original_point (j : Fin n) (s : unitInterval) :
    (interleavedSegments origin first last).point ⟨2 * j.val + 1, by omega⟩ s =
      AffineMap.lineMap (first j) (last j) (s : ℝ) := by
  let k : Fin (2 * n) := ⟨2 * j.val + 1, by omega⟩
  have before : k.castSucc = (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n + 1)) := rfl
  have after : k.succ = (⟨2 * (j.val + 1), by omega⟩ : Fin (2 * n + 1)) :=
    Fin.ext (by change 2 * j.val + 1 + 1 = 2 * (j.val + 1); omega)
  change (interleavedSegments origin first last).point k s = _
  rw [point, before, after, interleavedSegments_vertex_first, interleavedSegments_vertex_last]

theorem interleavedSegments_gap_point (j : Fin n) (s : unitInterval) :
    (interleavedSegments origin first last).point ⟨2 * j.val, by omega⟩ s =
      AffineMap.lineMap (segmentPredecessor origin last j) (first j) (s : ℝ) := by
  let k : Fin (2 * n) := ⟨2 * j.val, by omega⟩
  have before : k.castSucc = (⟨2 * j.val, by omega⟩ : Fin (2 * n + 1)) := rfl
  have after : k.succ = (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n + 1)) := rfl
  change (interleavedSegments origin first last).point k s = _
  rw [point, before, after, interleavedSegments_vertex_predecessor,
    interleavedSegments_vertex_first]

end Unfoldings.PolygonalChain
