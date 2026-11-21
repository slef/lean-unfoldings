module

public import Unfoldings.FewestNets.MeshBisectors
public import Mathlib.NumberTheory.Real.GoldenRatio

/-! Exact Cartesian coordinates and oriented facets of the regular icosahedron. -/

@[expose] public section

namespace Unfoldings.FewestNets.Icosahedron

open Real
open scoped BigOperators

/-- Integer coordinates in the basis of one and the golden ratio. -/
abbrev GoldenInt := ℤ × ℤ

def goldenMultiply (u v : GoldenInt) : GoldenInt :=
  (u.1 * v.1 + u.2 * v.2, u.1 * v.2 + u.2 * v.1 + u.2 * v.2)

noncomputable def goldenValue (u : GoldenInt) : ℝ := (u.1 : ℝ) + (u.2 : ℝ) * goldenRatio

theorem goldenValue_add (u v : GoldenInt) :
    goldenValue (u + v) = goldenValue u + goldenValue v := by
  simp only [goldenValue, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem goldenValue_multiply (u v : GoldenInt) :
    goldenValue (goldenMultiply u v) = goldenValue u * goldenValue v := by
  simp only [goldenValue, goldenMultiply, Int.cast_add, Int.cast_mul]
  linear_combination -((u.2 : ℝ) * (v.2 : ℝ)) * goldenRatio_sq

/-- The twelve vertices are cyclic coordinate permutations of the four sign choices. -/
def rawCoordinates : Fin 12 → Fin 3 → GoldenInt :=
  ![
    ![(0, 0), (-1, 0), (0, -1)],
    ![(0, 0), (-1, 0), (0, 1)],
    ![(0, 0), (1, 0), (0, -1)],
    ![(0, 0), (1, 0), (0, 1)],
    ![(0, -1), (0, 0), (-1, 0)],
    ![(0, 1), (0, 0), (-1, 0)],
    ![(0, -1), (0, 0), (1, 0)],
    ![(0, 1), (0, 0), (1, 0)],
    ![(-1, 0), (0, -1), (0, 0)],
    ![(-1, 0), (0, 1), (0, 0)],
    ![(1, 0), (0, -1), (0, 0)],
    ![(1, 0), (0, 1), (0, 0)]
  ]

/-- The twenty oriented occurrences of the mutually adjacent corner triples. -/
def faceVertex : Fin 20 → Fin 3 → Fin 12 :=
  ![
    ![0, 4, 2],
    ![0, 2, 5],
    ![0, 8, 4],
    ![0, 5, 10],
    ![0, 10, 8],
    ![1, 3, 6],
    ![1, 7, 3],
    ![1, 6, 8],
    ![1, 10, 7],
    ![1, 8, 10],
    ![2, 4, 9],
    ![2, 11, 5],
    ![2, 9, 11],
    ![3, 9, 6],
    ![3, 7, 11],
    ![3, 11, 9],
    ![4, 8, 6],
    ![4, 6, 9],
    ![5, 7, 10],
    ![5, 11, 7]
  ]

def dotData (i j : Fin 12) : GoldenInt :=
  ∑ k : Fin 3, goldenMultiply (rawCoordinates i k) (rawCoordinates j k)

noncomputable def rawVertex (i : Fin 12) : Space :=
  WithLp.toLp 2 (fun j => goldenValue (rawCoordinates i j))

theorem inner_rawVertex (i j : Fin 12) :
    inner ℝ (rawVertex i) (rawVertex j) = goldenValue (dotData i j) := by
  rw [inner_eq_coordinate_dotProduct, dotProduct, dotData, Fin.sum_univ_three, Fin.sum_univ_three,
    goldenValue_add, goldenValue_add, goldenValue_multiply, goldenValue_multiply,
    goldenValue_multiply]
  rfl

end Unfoldings.FewestNets.Icosahedron
