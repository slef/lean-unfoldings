module

public import Unfoldings.Geometry.Corner
public import Unfoldings.Geometry.EdgeSides
public import Mathlib.Tactic.Module

/-!
# Supporting wedges as positive spans of the actual edge rays

Barycentric coordinates give unique ray coefficients. This identifies the
previously constructed half-plane wedge with the usual positive-span sector
without assuming an angular parametrization.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- The positive-span expression is defined for all real coefficients. -/
def cornerCombination (T : Triangle) (i : Fin 3) (a b : ℝ) : Plane :=
  a • (T.vertex (next i) - T.vertex i) +
    b • (T.vertex (next (next i)) - T.vertex i) + T.vertex i

theorem coord_cornerCombination (T : Triangle) (i j : Fin 3) (a b : ℝ) :
    T.coord j (T.cornerCombination i a b) =
      a * (T.coord j (T.vertex (next i)) - T.coord j (T.vertex i)) +
        b * (T.coord j (T.vertex (next (next i))) - T.coord j (T.vertex i)) +
          T.coord j (T.vertex i) := by
  change (T.coord j) ((a • (T.vertex (next i) -ᵥ T.vertex i) +
    b • (T.vertex (next (next i)) -ᵥ T.vertex i)) +ᵥ T.vertex i) = _
  rw [(T.coord j).map_vadd, map_add, map_smul, map_smul,
    (T.coord j).linear_apply_vsub, (T.coord j).linear_apply_vsub]
  rfl

@[simp] theorem coord_next_cornerCombination (T : Triangle) (i : Fin 3) (a b : ℝ) :
    T.coord (next i) (T.cornerCombination i a b) = a := by
  rw [T.coord_cornerCombination]
  fin_cases i <;> simp [next]

@[simp] theorem coord_prev_cornerCombination (T : Triangle) (i : Fin 3) (a b : ℝ) :
    T.coord (next (next i)) (T.cornerCombination i a b) = b := by
  rw [T.coord_cornerCombination]
  fin_cases i <;> simp [next]

theorem reconstruct_corner (T : Triangle) (i : Fin 3) (x : Plane) :
    T.cornerCombination i (T.coord (next i) x) (T.coord (next (next i)) x) = x := by
  have coefficient : T.coord i x =
      1 - T.coord (next i) x - T.coord (next (next i)) x := by
    linarith [T.coord_sum_edge i x]
  symm
  calc
    x = T.coord i x • T.vertex i + T.coord (next i) x • T.vertex (next i) +
        T.coord (next (next i)) x • T.opposite i := T.reconstruct_edge i x
    _ = _ := by
      rw [coefficient]
      change (1 - T.coord (next i) x - T.coord (next (next i)) x) • T.vertex i +
        T.coord (next i) x • T.vertex (next i) +
          T.coord (next (next i)) x • T.vertex (next (next i)) = _
      dsimp only [cornerCombination]
      module

theorem cornerCombination_injective (T : Triangle) (i : Fin 3) :
    Function.Injective (fun p : ℝ × ℝ => T.cornerCombination i p.1 p.2) := by
  intro p q equal
  apply Prod.ext
  · simpa only [T.coord_next_cornerCombination] using congrArg (T.coord (next i)) equal
  · simpa only [T.coord_prev_cornerCombination] using
      congrArg (T.coord (next (next i))) equal

/-- The supporting wedge is exactly the positive span of its two actual boundary rays. -/
theorem mem_cornerWedge_iff_cornerCombination (T : Triangle) (i : Fin 3) (x : Plane) :
    x ∈ T.cornerWedge i ↔
      ∃ a ≥ 0, ∃ b ≥ 0, T.cornerCombination i a b = x := by
  constructor
  · intro inside
    exact ⟨T.coord (next i) x, inside.1, T.coord (next (next i)) x, inside.2,
      T.reconstruct_corner i x⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨by simpa using ha, by simpa using hb⟩

/-- Unique ray coefficients give coordinates on the entire ambient plane. -/
def cornerCombinationHomeomorph (T : Triangle) (i : Fin 3) : (ℝ × ℝ) ≃ₜ Plane where
  toFun p := T.cornerCombination i p.1 p.2
  invFun x := (T.coord (next i) x, T.coord (next (next i)) x)
  left_inv p := by
    apply Prod.ext <;> simp
  right_inv := T.reconstruct_corner i
  continuous_toFun := by
    change Continuous (fun p : ℝ × ℝ =>
      p.1 • (T.vertex (next i) - T.vertex i) +
        p.2 • (T.vertex (next (next i)) - T.vertex i) + T.vertex i)
    exact ((continuous_fst.smul continuous_const).add
      (continuous_snd.smul continuous_const)).add continuous_const
  continuous_invFun := (T.continuous_coord _).prodMk (T.continuous_coord _)

/-- Open wedge points are precisely the strictly positive combinations of the boundary rays. -/
theorem interior_cornerWedge (T : Triangle) (i : Fin 3) :
    interior (T.cornerWedge i) =
      {x | 0 < T.coord (next i) x ∧ 0 < T.coord (next (next i)) x} := by
  let h := T.cornerCombinationHomeomorph i
  have image : h '' (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) = T.cornerWedge i := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, inside, rfl⟩
      exact (T.mem_cornerWedge_iff_cornerCombination i _).mpr
        ⟨a, inside.1, b, inside.2, rfl⟩
    · intro inside
      exact ⟨(T.coord (next i) x, T.coord (next (next i)) x), inside,
        T.reconstruct_corner i x⟩
  rw [← image, ← h.image_interior, interior_prod_eq, interior_Ici]
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, positive, rfl⟩
    change 0 < a ∧ 0 < b at positive
    change 0 < T.coord (next i) (T.cornerCombination i a b) ∧
      0 < T.coord (next (next i)) (T.cornerCombination i a b)
    simpa only [T.coord_next_cornerCombination, T.coord_prev_cornerCombination]
      using positive
  · intro positive
    exact ⟨(T.coord (next i) x, T.coord (next (next i)) x), positive,
      T.reconstruct_corner i x⟩

end Unfoldings.Triangle
