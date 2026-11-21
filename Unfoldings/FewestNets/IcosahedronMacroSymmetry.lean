module

public import Unfoldings.FewestNets.IcosahedronSymmetries

/-! Isometries of the twelve original vertices induce permutations of the macrofaces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real

theorem rawVertex_injective : Function.Injective rawVertex := by
  intro i j same
  by_contra eq
  have h := inner_rawVertex_le_of_ne eq
  rw [← same, inner_rawVertex_self] at h
  linarith

theorem adjacent_of_inner_rawVertex_eq {i j : Fin 12}
    (h : inner ℝ (rawVertex i) (rawVertex j) = goldenRatio) : Adjacent i j := by
  have ne : i ≠ j := by
    rintro rfl
    rw [inner_rawVertex_self] at h
    linarith
  by_contra adj
  rw [inner_rawVertex, dotData_classify, ite_eq_right ne, ite_eq_right adj] at h
  split at h <;>
    dsimp only [goldenValue] at h <;> push_cast at h <;>
    linarith only [h, goldenRatio_pos]

/-- A spatial symmetry with the induced permutations of vertices and triangles. -/
structure MacroMeshSymmetry where
  frame : Space ≃ₗᵢ[ℝ] Space
  vertex : Equiv.Perm (Fin 12)
  face : Equiv.Perm (Fin 20)
  corner : Fin 20 → Equiv.Perm (Fin 3)
  vertex_eq (v : Fin 12) : frame (rawVertex v) = rawVertex (vertex v)
  corner_eq (f : Fin 20) (i : Fin 3) :
    faceVertex (face f) (corner f i) = vertex (faceVertex f i)

namespace MacroMeshSymmetry

theorem faceCorners_eq (S : MacroMeshSymmetry) (f : Fin 20) (i : Fin 3) :
    S.frame (faceCorners f i) = faceCorners (S.face f) (S.corner f i) := by
  change S.frame (rawVertex (faceVertex f i)) =
    rawVertex (faceVertex (S.face f) (S.corner f i))
  rw [S.vertex_eq, S.corner_eq]

/-- A linear isometry preserving the vertex set induces a macroface symmetry. -/
theorem exists_of_vertex_set (L : Space ≃ₗᵢ[ℝ] Space)
    (maps : ∀ v, ∃ w, L (rawVertex v) = rawVertex w) :
    ∃ S : MacroMeshSymmetry, S.frame = L := by
  choose move vertex_eq using maps
  have injective : Function.Injective move := fun _ _ h =>
    rawVertex_injective (L.injective ((vertex_eq _).trans
      ((congrArg rawVertex h).trans (vertex_eq _).symm)))
  let V := Equiv.ofBijective move (Finite.injective_iff_bijective.mp injective)
  have preserve {i j : Fin 12} (h : Adjacent i j) : Adjacent (V i) (V j) := by
    apply adjacent_of_inner_rawVertex_eq
    change inner ℝ (rawVertex (move i)) (rawVertex (move j)) = goldenRatio
    rw [← vertex_eq i, ← vertex_eq j, L.inner_map_map]
    exact inner_rawVertex_of_adjacent h
  have choose_macroface (f : Fin 20) :
      ∃ g : Fin 20, ∀ i : Fin 3, ∃ j : Fin 3, faceVertex g j = V (faceVertex f i) := by
    obtain ⟨g, h₀, h₁, h₂⟩ := exists_face_of_three
      (V (faceVertex f 0)) (V (faceVertex f 1)) (V (faceVertex f 2))
      (.inr (preserve (adjacent_faceVertex f (by decide))))
      (.inr (preserve (adjacent_faceVertex f (by decide))))
      (.inr (preserve (adjacent_faceVertex f (by decide))))
    refine ⟨g, fun i => ?_⟩
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  choose face labels using choose_macroface
  choose corner corner_eq using labels
  have ci (f : Fin 20) : Function.Injective (corner f) := fun i j eq => by
    apply (faceVertex_injective f)
    apply V.injective
    rw [← corner_eq f i, ← corner_eq f j, eq]
  let C (f : Fin 20) := Equiv.ofBijective (corner f) (Finite.injective_iff_bijective.mp (ci f))
  have fi : Function.Injective face := by
    intro f g eq
    apply face_eq_of_corner_subset
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, label⟩ := (C g).surjective (C f i)
    refine ⟨j, V.injective ?_⟩
    rw [← corner_eq g j, ← corner_eq f i, eq]
    exact congrArg (faceVertex (face g)) label
  exact ⟨⟨L, V, Equiv.ofBijective face (Finite.injective_iff_bijective.mp fi), C,
    vertex_eq, corner_eq⟩, rfl⟩

theorem exists_ordered (f : Fin 20) (σ : Equiv.Perm (Fin 3)) :
    ∃ S : MacroMeshSymmetry, S.face 0 = f ∧ S.corner 0 = σ := by
  obtain ⟨L, labels, maps⟩ := exists_isometry_ordered_macroface f σ
  obtain ⟨S, eq⟩ := exists_of_vertex_set L maps
  have same (i : Fin 3) : faceVertex (S.face 0) (S.corner 0 i) = faceVertex f (σ i) := by
    apply rawVertex_injective
    have h := S.faceCorners_eq 0 i
    rw [eq, labels] at h
    exact h.symm
  have f_eq : S.face 0 = f := by
    apply face_eq_of_corner_subset
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, eq⟩ := (S.corner 0).surjective i
    exact ⟨σ j, (same j).symm.trans (congrArg (faceVertex (S.face 0)) eq)⟩
  refine ⟨S, f_eq, Equiv.ext fun i => faceVertex_injective f ?_⟩
  exact f_eq ▸ same i

end MacroMeshSymmetry

end Unfoldings.FewestNets.Icosahedron
