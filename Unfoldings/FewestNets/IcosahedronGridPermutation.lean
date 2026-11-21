module

public import Unfoldings.FewestNets.IcosahedronSymmetries
public import Unfoldings.FewestNets.IcosahedronMeshFaceIdentity
public import Unfoldings.FewestNets.IcosahedronModelGrid

/-! Permuting the macroface coordinates preserves the fine triangular grid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace
open scoped BigOperators

/-- The minimum barycentric weights and the lower/upper label determine a fine cell. -/
def gridCellOfMin {q : ℕ} (b : Bool) (w : Fin 3 → ℕ)
    (total : (∑ i, w i) + (if b then 2 else 1) = q) : GridCell q := by
  rw [Fin.sum_univ_three] at total
  have i : w 1 < q + 1 := by split at total <;> omega
  have j : w 2 < q + 1 := by split at total <;> omega
  refine ⟨(⟨w 1, i⟩, ⟨w 2, j⟩, b), ?_⟩
  change TriangleGrid.Valid q (w 1) (w 2) b
  cases b <;> simp [TriangleGrid.Valid] at total ⊢ <;> omega

theorem localGridMin_gridCellOfMin {q : ℕ} (b : Bool) (w : Fin 3 → ℕ)
    (total : (∑ i, w i) + (if b then 2 else 1) = q) :
    localGridMin (gridCellOfMin b w total) = w := by
  rw [Fin.sum_univ_three] at total
  funext i
  fin_cases i
  · change q - (w 1 + w 2 + (if b then 2 else 1)) = w 0
    cases b <;> simp at total ⊢ <;> omega
  · rfl
  · rfl

def permuteGridCell {q : ℕ} (σ : Equiv.Perm (Fin 3)) (t : GridCell q) : GridCell q :=
  gridCellOfMin t.val.2.2 (localGridMin t ∘ σ.symm)
    (by
      change (∑ i, localGridMin t (σ.symm i)) + _ = _
      rw [Equiv.sum_comp]
      exact TriangleGrid.sum_barycentricMin t.property)

theorem localGridWeights_permuteGridCell {q : ℕ} (σ : Equiv.Perm (Fin 3))
    (t : GridCell q) (i j : Fin 3) :
    localGridWeights (permuteGridCell σ t) (σ i) (σ j) = localGridWeights t i j := by
  change localGridMin (permuteGridCell σ t) (σ j) +
      (if (σ j = σ i) ↔ t.val.2.2 = false then 1 else 0) =
      localGridMin t j + (if (j = i) ↔ t.val.2.2 = false then 1 else 0)
  simp [permuteGridCell, localGridMin_gridCellOfMin]

/-- A frame for any ordering of an actual macroface's unit vertices. -/
theorem exists_ordered_modelFace_isometry (f : Fin 20) (σ : Equiv.Perm (Fin 3)) :
    ∃ L : Space ≃ₗᵢ[ℝ] Space, ∀ i, L (modelCorners i) = unitFaceCorners f (σ i) := by
  obtain ⟨L₀, first⟩ := exists_modelFace_isometry 0
  obtain ⟨L₁, vertices, _⟩ := exists_isometry_ordered_macroface f σ
  refine ⟨L₀.trans L₁, fun i => ?_⟩
  change L₁ (L₀ (modelCorners i)) = _
  rw [first, unitFaceCorners, map_smul, vertices]
  rfl

/-- Any ordered isometric macroface frame transports every fine corner, in
the corresponding barycentric order. -/
theorem map_normalize_modelGridCorners_permute {q : ℕ} (hq : 0 < q) (f : Fin 20)
    (σ : Equiv.Perm (Fin 3)) (t : GridCell q) (L : Space ≃ₗᵢ[ℝ] Space)
    (map_corner : ∀ i, L (modelCorners i) = unitFaceCorners f (σ i)) (k : Fin 3) :
    L (normalize (modelGridCorners t k)) =
      inscribedCorners (f, permuteGridCell σ t) (σ k) := by
  have field : modelGridCorners t k =
      ∑ j, ((localGridWeights t k j : ℝ) / q) • modelCorners j := by
    obtain ⟨L₀, map₀⟩ := exists_modelFace_isometry 0
    apply L₀.injective
    rw [map_modelGridCorners (0, t) L₀ map₀, chordCorners_eq_localGridWeights hq,
      map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, map₀, unitFaceCorners, smul_comm]
  have chord : L (modelGridCorners t k) =
      radius⁻¹ • chordCorners (f, permuteGridCell σ t) (σ k) := by
    rw [field, chordCorners_eq_localGridWeights hq, map_sum, Finset.smul_sum]
    let weighted (j : Fin 3) := radius⁻¹ •
      (((localGridWeights (permuteGridCell σ t) (σ k) j : ℝ) / q) • faceCorners f j)
    change _ = ∑ j, weighted j
    rw [← Equiv.sum_comp σ weighted]
    apply Finset.sum_congr rfl
    intro j _
    change L (((localGridWeights t k j : ℝ) / q) • modelCorners j) =
      radius⁻¹ • (((localGridWeights (permuteGridCell σ t) (σ k) (σ j) : ℝ) / q) •
        faceCorners f (σ j))
    rw [map_smul, map_corner, unitFaceCorners, localGridWeights_permuteGridCell, smul_comm]
  have mapped : L (normalize (modelGridCorners t k)) = normalize (L (modelGridCorners t k)) := by
    simp only [NormedSpace.normalize, map_smul, LinearIsometryEquiv.norm_map]
  rw [mapped, chord, NormedSpace.normalize_smul_of_pos (inv_pos.mpr radius_pos)]
  rfl

end Unfoldings.FewestNets.Icosahedron
