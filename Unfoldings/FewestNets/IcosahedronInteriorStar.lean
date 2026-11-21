module

public import Unfoldings.FewestNets.IcosahedronModelGrid

/-! The six small triangles at an interior lattice site realize the canonical face star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real MeshStar
open TriangleGrid (Valid)

/-- Base square and orientation of each of the six small triangles at an interior site. -/
def faceStarCellKey (i j : ℕ) : Fin 6 → ℕ × ℕ × Bool :=
  ![(i, j, false), (i - 1, j, true), (i - 1, j, false), (i - 1, j - 1, true),
    (i, j - 1, false), (i, j - 1, true)]

theorem faceStarCellKey_valid {q i j : ℕ} (hi : 0 < i) (hj : 0 < j) (sum : i + j < q)
    (k : Fin 6) :
    let key := faceStarCellKey i j k
    Valid q key.1 key.2.1 key.2.2 := by
  fin_cases k <;> simp [faceStarCellKey, Valid] <;> omega

def faceStarCell {q i j : ℕ} (hi : 0 < i) (hj : 0 < j) (sum : i + j < q)
    (k : Fin 6) : GridCell q := by
  let t := faceStarCellKey i j k
  have valid := faceStarCellKey_valid hi hj sum k
  have ile : t.1 < q + 1 := by
    change Valid q t.1 t.2.1 t.2.2 at valid
    unfold Valid at valid
    split at valid <;> omega
  have jle : t.2.1 < q + 1 := by
    change Valid q t.1 t.2.1 t.2.2 at valid
    unfold Valid at valid
    split at valid <;> omega
  exact ⟨(⟨t.1, ile⟩, ⟨t.2.1, jle⟩, t.2.2), valid⟩

/-- For each cell, its center-site corner followed by its two cyclic neighbors. -/
def faceStarCornerIndex (k : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0], ![0, 1, 2], ![2, 0, 1], ![1, 2, 0]] k

theorem faceStarCornerIndex_bijective (k : Fin 6) : Function.Bijective (faceStarCornerIndex k) := by
  refine ⟨?_, ?_⟩
  · have table : ∀ k : Fin 6, ∀ i j : Fin 3, faceStarCornerIndex k i = faceStarCornerIndex k j →
        i = j := by decide +kernel
    exact fun _ _ => table k _ _
  · have table : ∀ k : Fin 6, ∀ i : Fin 3, ∃ j : Fin 3, faceStarCornerIndex k j = i := by
      decide +kernel
    exact table k

/-- The representative star with coordinates based at model corner A. -/
def modelInteriorStar (q i j : ℕ) : MeshStar 6 :=
  let z := TriangleGrid.point cornerA cornerB cornerC q i j
  ⟨z, fun k => z + faceOffset q k⟩

/-- Translate between the model grid coordinates and the certificate's face-key convention. -/
theorem modelInteriorStar_eq_face {q i j : ℕ} (sum : i + j < q) :
    modelInteriorStar q i j = face q i (q - i - j) := by
  have sub : ((q - i - j : ℕ) : ℝ) = (q : ℝ) - i - j := by
    rw [Nat.cast_sub (by omega : j ≤ q - i), Nat.cast_sub (by omega : i ≤ q)]
  have ne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have coeff : ((q : ℝ) - i - j) / q = 1 - (i : ℝ) / q - (j : ℝ) / q := by
    field_simp
  have site : TriangleGrid.point cornerA cornerB cornerC q i j =
      cornerC + ((i : ℝ) / q) • (cornerB - cornerC) +
        (((q - i - j : ℕ) : ℝ) / q) • (cornerA - cornerC) := by
    rw [sub, coeff]
    unfold TriangleGrid.point
    module
  simp only [modelInteriorStar, face, site]

/-- Each actual model triangle lists exactly the site and two consecutive neighbors. -/
theorem modelGridCorners_faceStarCell {q i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (sum : i + j < q) (k : Fin 6) (l : Fin 3) :
    modelGridCorners (faceStarCell hi hj sum k) (faceStarCornerIndex k l) =
      (![(modelInteriorStar q i j).site, (modelInteriorStar q i j).neighbor k,
        (modelInteriorStar q i j).neighbor (k + 1)] : Fin 3 → Space) l := by
  have i_sub : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi, Nat.cast_one]
  have j_sub : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj, Nat.cast_one]
  fin_cases k <;> fin_cases l <;>
    simp [modelGridCorners, faceStarCell, faceStarCellKey, faceStarCornerIndex, modelInteriorStar,
      TriangleGrid.cellCorners, TriangleGrid.point, TriangleGrid.corner, faceOffset, stepU, stepV,
      Fin.add_def, Nat.cast_add, i_sub, j_sub, add_div, sub_div] <;> module

end Unfoldings.FewestNets.Icosahedron
