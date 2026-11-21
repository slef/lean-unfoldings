module

public import Unfoldings.FewestNets.IcosahedronFacets

/-! The macroface intersections are exactly the hulls of their common corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real

theorem inner_faceNormal_rawVertex_eq_iff (f : Fin 20) (i : Fin 12) :
    inner ℝ (faceNormal f) (rawVertex i) = 2 + 3 * goldenRatio ↔
      i ∈ Set.range (faceVertex f) := by
  refine ⟨fun eq => ?_, ?_⟩
  · by_contra outside
    exact (inner_faceNormal_lt_of_outside f outside).ne eq
  · rintro ⟨k, rfl⟩
    exact inner_faceNormal_corner f k

/-- Two macrofaces meet in the convex hull of their common raw corners. -/
theorem faceTriangle_inter (f g : Fin 20) :
    faceTriangle f ∩ faceTriangle g =
      convexHull ℝ (rawVertex '' (Set.range (faceVertex f) ∩ Set.range (faceVertex g))) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hf, hg⟩
    rw [faceTriangle_eq_support] at hf hg
    let n := faceNormal f + faceNormal g
    let m := (2 + 3 * goldenRatio) + (2 + 3 * goldenRatio)
    have bound (i : Fin 12) : inner ℝ n (rawVertex i) ≤ m := by
      dsimp only [n]
      rw [inner_add_left]
      exact add_le_add (inner_faceNormal_rawVertex_le f i) (inner_faceNormal_rawVertex_le g i)
    have eq : inner ℝ n x = m := by
      dsimp only [n]
      rw [inner_add_left, hf.2, hg.2]
    have sub : rawVertex '' {i | inner ℝ n (rawVertex i) = m} ⊆
        rawVertex '' (Set.range (faceVertex f) ∩ Set.range (faceVertex g)) := by
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨i, ⟨(inner_faceNormal_rawVertex_eq_iff f i).mp ?_,
        (inner_faceNormal_rawVertex_eq_iff g i).mp ?_⟩, rfl⟩
      all_goals
        change inner ℝ n (rawVertex i) = m at hi
        dsimp only [n] at hi
        rw [inner_add_left] at hi
        dsimp only [m] at hi
        linarith only [hi, inner_faceNormal_rawVertex_le f i, inner_faceNormal_rawVertex_le g i]
    exact convexHull_mono sub (mem_convexHull_maximizingCorners bound hf.1 eq)
  · refine Set.subset_inter (convexHull_mono ?_) (convexHull_mono ?_)
    · rintro _ ⟨i, ⟨⟨j, rfl⟩, _⟩, rfl⟩
      exact Set.mem_range_self j
    · rintro _ ⟨i, ⟨_, ⟨j, rfl⟩⟩, rfl⟩
      exact Set.mem_range_self j

/-- A pair of macrofaces with all three corners in common has identical labels. -/
theorem face_eq_of_corner_subset {f g : Fin 20}
    (sub : Set.range (faceVertex f) ⊆ Set.range (faceVertex g)) : f = g := by
  have table : ∀ f g : Fin 20,
      (∀ i : Fin 3, ∃ j : Fin 3, faceVertex g j = faceVertex f i) → f = g := by
    decide +kernel
  exact table f g (fun i => sub (Set.mem_range_self i))

end Unfoldings.FewestNets.Icosahedron
