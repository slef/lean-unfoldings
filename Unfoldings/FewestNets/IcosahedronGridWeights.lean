module

public import Unfoldings.FewestNets.IcosahedronSubdivision
public import Unfoldings.Geometry.TriangleGridBarycentric

/-! Index fine vertices by their integer weights on the twelve original corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

/-- Extend three corner weights by zero outside their macroface. -/
def extendFaceWeights {R : Type*} [AddCommMonoid R] (f : Fin 20) (w : Fin 3 → R)
    (i : Fin 12) : R :=
  ∑ d, if faceVertex f d = i then w d else 0

theorem extendFaceWeights_faceVertex {R : Type*} [AddCommMonoid R] (f : Fin 20)
    (w : Fin 3 → R) (d : Fin 3) : extendFaceWeights f w (faceVertex f d) = w d := by
  have test (j : Fin 3) : faceVertex f j = faceVertex f d ↔ j = d :=
    (faceVertex_injective f).eq_iff
  simp [extendFaceWeights, test]

theorem extendFaceWeights_zero_of_outside {R : Type*} [AddCommMonoid R] (f : Fin 20)
    (w : Fin 3 → R) {i : Fin 12} (hi : i ∉ Set.range (faceVertex f)) :
    extendFaceWeights f w i = 0 := by
  have test (d : Fin 3) : faceVertex f d ≠ i := fun h => hi ⟨d, h⟩
  simp [extendFaceWeights, test]

theorem sum_extendFaceWeights {R : Type*} [AddCommMonoid R] (f : Fin 20) (w : Fin 3 → R) :
    (∑ i : Fin 12, extendFaceWeights f w i) = ∑ d, w d := by
  simp only [extendFaceWeights]
  rw [Finset.sum_comm]
  simp

theorem sum_extendFaceWeights_smul (f : Fin 20) (w : Fin 3 → ℝ) :
    (∑ i : Fin 12, extendFaceWeights f w i • rawVertex i) = ∑ d, w d • faceCorners f d := by
  simp only [extendFaceWeights, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp [faceCorners]

def localGridWeights {q : ℕ} (t : GridCell q) (k : Fin 3) : Fin 3 → ℕ :=
  TriangleGrid.barycentricCorner q t.val.1.val t.val.2.1.val t.val.2.2 k

def gridWeights {q : ℕ} (t : MeshFace q) (k : Fin 3) : Fin 12 → ℕ :=
  extendFaceWeights t.1 (localGridWeights t.2 k)

theorem sum_localGridWeights {q : ℕ} (t : GridCell q) (k : Fin 3) :
    (∑ d, localGridWeights t k d) = q :=
  TriangleGrid.sum_barycentricCorner t.property k

theorem sum_gridWeights {q : ℕ} (t : MeshFace q) (k : Fin 3) :
    (∑ i, gridWeights t k i) = q :=
  (sum_extendFaceWeights _ _).trans (sum_localGridWeights t.2 k)

theorem chordCorners_eq_localGridWeights {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    chordCorners t k = ∑ d, ((localGridWeights t.2 k d : ℝ) / q) • faceCorners t.1 d := by
  let w := localGridWeights t.2 k
  let z := faceCorners t.1
  have total : (w 0 : ℝ) + w 1 + w 2 = q := by
    have h := sum_localGridWeights t.2 k
    rw [Fin.sum_univ_three] at h
    exact_mod_cast h
  have qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have first : (w 0 : ℝ) / q = 1 - (w 1 : ℝ) / q - (w 2 : ℝ) / q := by
    field_simp
    linarith only [total]
  rw [Fin.sum_univ_three]
  change chordCorners t k = (w 0 / (q : ℝ)) • z 0 + (w 1 / (q : ℝ)) • z 1 + (w 2 / (q : ℝ)) • z 2
  rw [first]
  unfold chordCorners TriangleGrid.cellCorners TriangleGrid.point
  rw [← TriangleGrid.barycentricCorner_one q, ← TriangleGrid.barycentricCorner_two q]
  change z 0 + (w 1 / (q : ℝ)) • (z 1 - z 0) + (w 2 / (q : ℝ)) • (z 2 - z 0) = _
  module

/-- The same twelve integer weights identify a fine vertex across macroface boundaries. -/
theorem chordCorners_eq_gridWeights {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    chordCorners t k = ∑ i, ((gridWeights t k i : ℝ) / q) • rawVertex i := by
  rw [chordCorners_eq_localGridWeights hq]
  rw [← sum_extendFaceWeights_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  by_cases inside : i ∈ Set.range (faceVertex t.1)
  · obtain ⟨d, rfl⟩ := inside
    rw [extendFaceWeights_faceVertex, gridWeights, extendFaceWeights_faceVertex]
  · rw [extendFaceWeights_zero_of_outside _ _ inside, gridWeights,
      extendFaceWeights_zero_of_outside _ _ inside]
    simp

end Unfoldings.FewestNets.Icosahedron
