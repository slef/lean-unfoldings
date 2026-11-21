module

public import Unfoldings.FewestNets.IcosahedronGridWeights

/-! Integer boxes describe fine-cell corners even across different macrofaces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

def localGridMin {q : ℕ} (t : GridCell q) : Fin 3 → ℕ :=
  TriangleGrid.barycentricMin q t.val.1.val t.val.2.1.val t.val.2.2

def gridMin {q : ℕ} (t : MeshFace q) : Fin 12 → ℕ :=
  extendFaceWeights t.1 (localGridMin t.2)

def gridMax {q : ℕ} (t : MeshFace q) (i : Fin 12) : ℕ := by
  classical
  exact if i ∈ Set.range (faceVertex t.1) then gridMin t i + 1 else 0

theorem gridWeights_bounds {q : ℕ} (t : MeshFace q) (k : Fin 3) (i : Fin 12) :
    gridMin t i ≤ gridWeights t k i ∧ gridWeights t k i ≤ gridMax t i := by
  classical
  by_cases inside : i ∈ Set.range (faceVertex t.1)
  · obtain ⟨d, rfl⟩ := inside
    have yes : faceVertex t.1 d ∈ Set.range (faceVertex t.1) := Set.mem_range_self d
    rw [gridMax, ite_eq_left yes, gridMin, gridWeights,
      extendFaceWeights_faceVertex, extendFaceWeights_faceVertex]
    exact TriangleGrid.barycentricCorner_bounds _ _ _ _ _ d
  · rw [gridMax, ite_eq_right inside, gridMin, gridWeights,
      extendFaceWeights_zero_of_outside _ _ inside, extendFaceWeights_zero_of_outside _ _ inside]
    simp

theorem gridMax_le_gridMin_succ {q : ℕ} (t : MeshFace q) (i : Fin 12) :
    gridMax t i ≤ gridMin t i + 1 := by
  classical
  unfold gridMax
  split <;> omega

/-- The integer points in the box at total weight q are exactly the cell's corners. -/
theorem exists_gridWeights_of_bounds {q : ℕ} (t : MeshFace q) (w : Fin 12 → ℕ)
    (sum : ∑ i, w i = q)
    (bounds : ∀ i, gridMin t i ≤ w i ∧ w i ≤ gridMax t i) :
    ∃ k : Fin 3, gridWeights t k = w := by
  classical
  have supported (i : Fin 12) (outside : i ∉ Set.range (faceVertex t.1)) : w i = 0 := by
    have le := (bounds i).2
    rw [gridMax, ite_eq_right outside] at le
    omega
  let v := w ∘ faceVertex t.1
  have ext : extendFaceWeights t.1 v = w := by
    funext i
    by_cases inside : i ∈ Set.range (faceVertex t.1)
    · obtain ⟨d, rfl⟩ := inside
      exact extendFaceWeights_faceVertex _ _ _
    · rw [extendFaceWeights_zero_of_outside _ _ inside, supported _ inside]
  have total : ∑ d, v d = q := by
    rw [← sum_extendFaceWeights t.1 v, ext, sum]
  have local_bounds (d : Fin 3) :
      localGridMin t.2 d ≤ v d ∧ v d ≤ localGridMin t.2 d + 1 := by
    have h := bounds (faceVertex t.1 d)
    have yes : faceVertex t.1 d ∈ Set.range (faceVertex t.1) := Set.mem_range_self d
    rw [gridMax, ite_eq_left yes, gridMin, extendFaceWeights_faceVertex] at h
    exact h
  obtain ⟨k, hk⟩ :=
    TriangleGrid.exists_barycentricCorner_of_bounds t.2.property v total local_bounds
  refine ⟨k, ?_⟩
  have eq : localGridWeights t.2 k = v := hk
  rw [gridWeights, eq, ext]

end Unfoldings.FewestNets.Icosahedron
