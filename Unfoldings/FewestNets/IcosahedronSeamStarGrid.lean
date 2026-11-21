module

public import Unfoldings.FewestNets.IcosahedronModelGrid
public import Unfoldings.FewestNets.IcosahedronGridWeights

/-! The three fine triangles at a macroedge site on one side of the seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar TriangleGrid

def seamBaseCellKey (i : ℕ) : Fin 3 → ℕ × ℕ × Bool :=
  ![(i, 0, false), (i - 1, 0, true), (i - 1, 0, false)]

theorem seamBaseCellKey_valid {q i : ℕ} (hi : 0 < i) (last : i < q) (k : Fin 3) :
    let label := seamBaseCellKey i k
    Valid q label.1 label.2.1 label.2.2 := by
  fin_cases k <;> simp [seamBaseCellKey, Valid] <;> omega

def seamBaseCell {q i : ℕ} (hi : 0 < i) (last : i < q) (k : Fin 3) : GridCell q := by
  let t := seamBaseCellKey i k
  have valid := seamBaseCellKey_valid hi last k
  have first : t.1 < q + 1 := by
    change Valid q t.1 t.2.1 t.2.2 at valid
    unfold Valid at valid
    split at valid <;> omega
  have second : t.2.1 < q + 1 := by
    change Valid q t.1 t.2.1 t.2.2 at valid
    unfold Valid at valid
    split at valid <;> omega
  exact ⟨(⟨t.1, first⟩, ⟨t.2.1, second⟩, t.2.2), valid⟩

theorem seamBaseCell_injective {q i : ℕ} (hi : 0 < i) (last : i < q) :
    Function.Injective (seamBaseCell hi last) := by
  intro k l equal
  have keys : seamBaseCellKey i k = seamBaseCellKey i l :=
    congrArg (fun t : GridCell q => (t.val.1.val, t.val.2.1.val, t.val.2.2)) equal
  fin_cases k <;> fin_cases l <;> simp [seamBaseCellKey] at keys ⊢ <;> omega

def seamBaseCornerIndex (k : Fin 3) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]] k

theorem seamBaseCornerIndex_bijective (k : Fin 3) : Function.Bijective (seamBaseCornerIndex k) := by
  refine ⟨?_, ?_⟩
  · have table : ∀ k : Fin 3, ∀ i j : Fin 3, seamBaseCornerIndex k i = seamBaseCornerIndex k j →
        i = j := by decide +kernel
    exact fun _ _ => table k _ _
  · have table : ∀ k : Fin 3, ∀ i : Fin 3, ∃ j : Fin 3, seamBaseCornerIndex k j = i := by
      decide +kernel
    exact table k

def seamBaseIndex (k : Fin 3) : Fin 6 := ⟨k.val, k.isLt.trans (by decide)⟩

set_option maxHeartbeats 1000000 in
-- Expand the three grid triangles in the macroface frame.
theorem modelGridCorners_seamBaseCell {q i : ℕ} (hi : 0 < i) (last : i < q)
    (k l : Fin 3) :
    modelGridCorners (seamBaseCell hi last k) (seamBaseCornerIndex k l) =
      (![(seam q i).site, (seam q i).neighbor (seamBaseIndex k),
        (seam q i).neighbor (seamBaseIndex k + 1)] : Fin 3 → Space) l := by
  have i_sub : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi, Nat.cast_one]
  fin_cases k <;> fin_cases l <;>
    simp [seam, seamNeighbor, seamBaseIndex, modelGridCorners, seamBaseCell, seamBaseCellKey,
      seamBaseCornerIndex, TriangleGrid.cellCorners, TriangleGrid.point, TriangleGrid.corner,
      stepU, stepV, Fin.add_def, Nat.cast_add, i_sub, add_div, sub_div] <;> module

theorem localGridWeights_seamBaseCell_zero {q i : ℕ} (hi : 0 < i) (last : i < q) :
    localGridWeights (seamBaseCell hi last 0) 0 = ![q - i, i, 0] := by
  funext d
  fin_cases d <;> simp [localGridWeights, seamBaseCell, seamBaseCellKey, barycentricCorner,
    barycentricMin]
  omega

private theorem exists_seamBaseCellKey_of_corner {i x y : ℕ} (b : Bool) (k : Fin 3)
    (equal : corner x y b k = (i, 0)) :
    ∃ l : Fin 3, (x, y, b) = seamBaseCellKey i l := by
  cases b
  · fin_cases k
    · exact ⟨0, by simp [corner, seamBaseCellKey] at equal ⊢; omega⟩
    · exact ⟨2, by simp [corner, seamBaseCellKey] at equal ⊢; omega⟩
    · simp [corner] at equal
  · fin_cases k
    · simp [corner] at equal
    · simp [corner] at equal
    · exact ⟨1, by simp [corner, seamBaseCellKey] at equal ⊢; omega⟩

theorem exists_seamBaseCell_of_weights {q i : ℕ} (hi : 0 < i) (last : i < q)
    (t : GridCell q) (k : Fin 3) (first : localGridWeights t k 1 = i)
    (second : localGridWeights t k 2 = 0) :
    ∃ l : Fin 3, t = seamBaseCell hi last l := by
  change barycentricCorner q _ _ _ k 1 = i at first
  change barycentricCorner q _ _ _ k 2 = 0 at second
  rw [barycentricCorner_one] at first
  rw [barycentricCorner_two] at second
  obtain ⟨l, label⟩ := exists_seamBaseCellKey_of_corner t.val.2.2 k (Prod.ext first second)
  refine ⟨l, Subtype.ext (Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) ?_))⟩
  · exact congrArg Prod.fst label
  · exact congrArg (fun p : ℕ × ℕ × Bool => p.2.1) label
  · exact congrArg (fun p : ℕ × ℕ × Bool => p.2.2) label

end Unfoldings.FewestNets.Icosahedron
