module

public import Unfoldings.FewestNets.IcosahedronCoordinates

/-! Exact adjacency and supporting-face tests for the twelve icosahedral corners. -/

@[expose] public section

namespace Unfoldings.FewestNets.Icosahedron

open Real

/-- Two distinct corners are neighbors exactly when their unscaled dot product is `φ`. -/
def Adjacent (i j : Fin 12) : Prop := dotData i j = (0, 1)
deriving Decidable

theorem dotData_classify (i j : Fin 12) :
    dotData i j = if i = j then (2, 1) else
      if Adjacent i j then (0, 1) else if dotData i j = (0, -1) then (0, -1) else (-2, -1) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- For a pair at the longer non-antipodal distance, another pair has a
sum on the same ray, farther from the origin by a factor of `φ`. -/
theorem exists_pair_beyond (i j : Fin 12) (h : dotData i j = (0, -1)) :
    ∃ a b : Fin 12, rawVertex a + rawVertex b = goldenRatio • (rawVertex i + rawVertex j) := by
  have table : ∀ i j : Fin 12, dotData i j = (0, -1) →
      ∃ a b : Fin 12, ∀ k : Fin 3,
        rawCoordinates a k + rawCoordinates b k =
          goldenMultiply (0, 1) (rawCoordinates i k + rawCoordinates j k) := by
    decide +kernel
  obtain ⟨a, b, hab⟩ := table i j h
  refine ⟨a, b, ?_⟩
  ext k
  change goldenValue (rawCoordinates a k) + goldenValue (rawCoordinates b k) =
    goldenRatio * (goldenValue (rawCoordinates i k) + goldenValue (rawCoordinates j k))
  simpa only [goldenValue_add, goldenValue_multiply, show goldenValue (0, 1) = goldenRatio by
    simp [goldenValue]] using congrArg goldenValue (hab k)

def antipode (i : Fin 12) : Fin 12 :=
  ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8] i

theorem rawVertex_antipode (i : Fin 12) : rawVertex (antipode i) = -rawVertex i := by
  have table : ∀ i : Fin 12, ∀ k : Fin 3,
      rawCoordinates (antipode i) k = -rawCoordinates i k := by decide +kernel
  ext k
  change goldenValue (rawCoordinates (antipode i) k) = -goldenValue (rawCoordinates i k)
  rw [table]
  simp only [goldenValue, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem dotData_antipode_of_eq (i j : Fin 12) (h : dotData i j = (-2, -1)) :
    j = antipode i := by
  have table : ∀ i j : Fin 12, dotData i j = (-2, -1) → j = antipode i := by decide +kernel
  exact table i j h

theorem faceVertex_injective (f : Fin 20) : Function.Injective (faceVertex f) := by
  have table : ∀ (f : Fin 20) (i j : Fin 3), faceVertex f i = faceVertex f j → i = j := by
    decide +kernel
  exact fun _ _ => table f _ _

theorem adjacent_faceVertex (f : Fin 20) {i j : Fin 3} (ne : i ≠ j) :
    Adjacent (faceVertex f i) (faceVertex f j) := by
  have table : ∀ (f : Fin 20) (i j : Fin 3),
      i ≠ j → Adjacent (faceVertex f i) (faceVertex f j) := by
    decide +kernel
  exact table f i j ne

/-- A three-corner clique, allowing repeated inputs, lies in one of the twenty faces. -/
theorem exists_face_of_three (i j k : Fin 12) (ij : i = j ∨ Adjacent i j)
    (ik : i = k ∨ Adjacent i k) (jk : j = k ∨ Adjacent j k) :
    ∃ f : Fin 20, i ∈ Set.range (faceVertex f) ∧
      j ∈ Set.range (faceVertex f) ∧ k ∈ Set.range (faceVertex f) := by
  have table : ∀ i j k : Fin 12,
      (i = j ∨ Adjacent i j) → (i = k ∨ Adjacent i k) → (j = k ∨ Adjacent j k) →
      ∃ f : Fin 20, (∃ a : Fin 3, faceVertex f a = i) ∧
        (∃ b : Fin 3, faceVertex f b = j) ∧ (∃ c : Fin 3, faceVertex f c = k) := by
    decide +kernel
  exact table i j k ij ik jk

theorem mem_face_of_adjacent (f : Fin 20) (i : Fin 12)
    (h : ∀ j : Fin 3, i = faceVertex f j ∨ Adjacent i (faceVertex f j)) :
    i ∈ Set.range (faceVertex f) := by
  have table : ∀ (f : Fin 20) (i : Fin 12),
      (∀ j : Fin 3, i = faceVertex f j ∨ Adjacent i (faceVertex f j)) →
      ∃ j : Fin 3, faceVertex f j = i := by
    decide +kernel
  exact table f i h

end Unfoldings.FewestNets.Icosahedron
