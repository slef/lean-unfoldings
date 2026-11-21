module

public import Unfoldings.FewestNets.IcosahedronFacetNormals

/-! A verified candidate star normal agrees with the actual supporting-face normal. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace

theorem facetNormal_eq_normalize_of_constant_inner {q : ℕ} (hq : 0 < q) (t : MeshFace q)
    (m : Space) {h : ℝ} (positive : 0 < h)
    (constant : ∀ k, inner ℝ m (inscribedCorners t k) = h) :
    facetNormal hq t = NormedSpace.normalize m := by
  let L := h⁻¹ • (innerSL ℝ m).toLinearMap
  have values (k : Fin 3) : L (inscribedCorners t k) = 1 := by
    change h⁻¹ * inner ℝ m (inscribedCorners t k) = 1
    rw [constant, inv_mul_cancel₀ positive.ne']
  have plane : meshGauge hq t = L :=
    radialTriangleGauge_unique (linearIndependent_inscribedCorners hq t) L values
  have same : rawFacetNormal hq t = h⁻¹ • m := by
    apply ext_inner_right ℝ
    intro z
    rw [inner_rawFacetNormal, plane, real_inner_smul_left]
    rfl
  rw [facetNormal, same, normalize_smul_of_pos (inv_pos.mpr positive)]

/-- The checker normal is the actual normal of the corresponding triangle
whenever the cross product points toward its shared site. -/
theorem facetNormal_eq_map_dualDirection {q n : ℕ} (hq : 0 < q) (t : MeshFace q)
    (M : MeshStar (n + 1)) (k : Fin (n + 1)) (e : Space ≃ₗᵢ[ℝ] Space) (p : Fin 3 → Fin 3)
    (surjective : Function.Surjective p)
    (corner_eq : ∀ l : Fin 3, inscribedCorners t (p l) =
      e ((![M.direction, M.neighborDirection k, M.neighborDirection (k + 1)] : Fin 3 → Space) l))
    (positive : 0 < inner ℝ (M.dual k) M.direction) :
    facetNormal hq t = e (M.dualDirection k) := by
  have first : inner ℝ (M.dual k) (M.neighborDirection k) = inner ℝ (M.dual k) M.direction := by
    rw [real_inner_comm (M.neighborDirection k) (M.dual k), real_inner_comm M.direction (M.dual k)]
    exact (MeshStar.inner_dual_eq_neighbors M k).1.symm
  have second : inner ℝ (M.dual k) (M.neighborDirection (k + 1)) =
      inner ℝ (M.dual k) M.direction := by
    rw [real_inner_comm (M.neighborDirection (k + 1)) (M.dual k),
      real_inner_comm M.direction (M.dual k)]
    exact (MeshStar.inner_dual_eq_neighbors M k).2.symm
  rw [facetNormal_eq_normalize_of_constant_inner hq t (e (M.dual k)) positive]
  · simp only [MeshStar.dualDirection, NormedSpace.normalize, map_smul,
      LinearIsometryEquiv.norm_map]
  · intro l
    obtain ⟨j, rfl⟩ := surjective l
    rw [corner_eq, e.inner_map_map]
    fin_cases j
    · rfl
    · exact first
    · exact second

end Unfoldings.FewestNets.Icosahedron
