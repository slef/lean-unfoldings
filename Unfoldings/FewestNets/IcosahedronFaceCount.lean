module

public import Unfoldings.FewestNets.IcosahedronSubdivision

/-! A frequency-q grid has q squared triangles per macroface. -/

public section

namespace Unfoldings.FewestNets.Icosahedron

open TriangleGrid (Valid)

private def reverseIndex {q : ℕ} (i : Fin q) : Fin q :=
  ⟨q - 1 - i.val, by have h := i.isLt; omega⟩

private theorem reverseIndex_involution {q : ℕ} (i : Fin q) :
    reverseIndex (reverseIndex i) = i := by
  apply Fin.ext
  dsimp [reverseIndex]
  have h := i.isLt
  omega

private theorem firstGrid_lt {q : ℕ} (t : GridCell q) : t.val.1.val < q := by
  have h := t.property
  unfold Valid at h
  split at h <;> omega

private theorem secondGrid_lt {q : ℕ} (t : GridCell q) : t.val.2.1.val < q := by
  have h := t.property
  unfold Valid at h
  split at h <;> omega

private def lowerCell {q : ℕ} (x : Fin q × Fin q) (h : x.1.val + x.2.val < q) : GridCell q :=
  ⟨(x.1.castSucc, x.2.castSucc, false), by simp [Valid]; omega⟩

private def upperCell {q : ℕ} (x : Fin q × Fin q) (h : q ≤ x.1.val + x.2.val) : GridCell q :=
  ⟨((reverseIndex x.1).castSucc, (reverseIndex x.2).castSucc, true), by
    have h₁ := x.1.isLt
    have h₂ := x.2.isLt
    simp [Valid, reverseIndex]
    omega⟩

private def cellToSquare {q : ℕ} (t : GridCell q) : Fin q × Fin q :=
  let i : Fin q := ⟨t.val.1.val, firstGrid_lt t⟩
  let j : Fin q := ⟨t.val.2.1.val, secondGrid_lt t⟩
  if t.val.2.2 then (reverseIndex i, reverseIndex j) else (i, j)

private def squareToCell {q : ℕ} (x : Fin q × Fin q) : GridCell q :=
  if h : x.1.val + x.2.val < q then lowerCell x h else upperCell x (le_of_not_gt h)

private theorem cellToSquare_lowerCell {q : ℕ} (x : Fin q × Fin q)
    (h : x.1.val + x.2.val < q) : cellToSquare (lowerCell x h) = x := by
  rcases x with ⟨i, j⟩
  rfl

private theorem cellToSquare_upperCell {q : ℕ} (x : Fin q × Fin q)
    (h : q ≤ x.1.val + x.2.val) : cellToSquare (upperCell x h) = x := by
  rcases x with ⟨i, j⟩
  change (reverseIndex (reverseIndex i), reverseIndex (reverseIndex j)) = (i, j)
  rw [reverseIndex_involution, reverseIndex_involution]

/-- The upper triangles occupy the reflected complement of the lower triangles
in the square of grid indices. -/
def gridCellEquivSquare (q : ℕ) : GridCell q ≃ Fin q × Fin q where
  toFun := cellToSquare
  invFun := squareToCell
  left_inv t := by
    rcases t with ⟨⟨i, j, upper⟩, valid⟩
    have hi := firstGrid_lt (⟨(i, j, upper), valid⟩ : GridCell q)
    have hj := secondGrid_lt (⟨(i, j, upper), valid⟩ : GridCell q)
    change i.val < q at hi
    change j.val < q at hj
    cases upper
    · have lower : i.val + j.val < q := by simp [Valid] at valid; omega
      have same : cellToSquare (⟨(i, j, false), valid⟩ : GridCell q) =
          (⟨i.val, hi⟩, ⟨j.val, hj⟩) := rfl
      rw [same, squareToCell, dite_eq_left lower]
      rfl
    · have above : ¬q - 1 - i.val + (q - 1 - j.val) < q := by
        simp [Valid] at valid
        omega
      have same : cellToSquare (⟨(i, j, true), valid⟩ : GridCell q) =
          (reverseIndex ⟨i.val, hi⟩, reverseIndex ⟨j.val, hj⟩) := rfl
      rw [same, squareToCell, dite_eq_right (show
        ¬(reverseIndex (⟨i.val, hi⟩ : Fin q)).val + (reverseIndex (⟨j.val, hj⟩ : Fin q)).val < q
        from above)]
      apply Subtype.ext
      change (((reverseIndex (reverseIndex (⟨i.val, hi⟩ : Fin q))).castSucc),
        ((reverseIndex (reverseIndex (⟨j.val, hj⟩ : Fin q))).castSucc), true) = (i, j, true)
      rw [reverseIndex_involution, reverseIndex_involution]
      rfl
  right_inv x := by
    unfold squareToCell
    split
    · exact cellToSquare_lowerCell x _
    · exact cellToSquare_upperCell x _

theorem card_gridCell (q : ℕ) : Nat.card (GridCell q) = q ^ 2 := by
  rw [Nat.card_congr (gridCellEquivSquare q), Nat.card_prod, Nat.card_fin, pow_two]

theorem card_meshFace (q : ℕ) : Nat.card (MeshFace q) = 20 * q ^ 2 := by
  rw [Nat.card_prod, Nat.card_fin, card_gridCell]

end Unfoldings.FewestNets.Icosahedron
