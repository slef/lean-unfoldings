module

public import Unfoldings.FewestNets.IcosahedronSubdivision
public import Unfoldings.Geometry.TriangleGridEdges

/-! Geometry of a canonical small grid triangle, expressed in the model face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real MeshStar NormedSpace

def modelGridCorners {q : ℕ} (t : GridCell q) : Fin 3 → Space :=
  TriangleGrid.cellCorners cornerA cornerB cornerC q t.val.1.val t.val.2.1.val t.val.2.2

private theorem modelCorner_norm (i : Fin 3) : ‖modelCorners i‖ = 1 := by
  fin_cases i
  · exact cornerA_unit
  · exact cornerB_unit
  · exact cornerC_unit

private theorem modelGrid_mem_modelTriangle {q : ℕ} (hq : 0 < q) (t : GridCell q) (k : Fin 3) :
    modelGridCorners t k ∈ convexHull ℝ (Set.range modelCorners) :=
  TriangleGrid.cell_subset_triangle cornerA cornerB cornerC hq t.property
    (subset_convexHull ℝ _ (Set.mem_range_self k))

theorem norm_modelGridCorners_le_one {q : ℕ} (hq : 0 < q) (t : GridCell q) (k : Fin 3) :
    ‖modelGridCorners t k‖ ≤ 1 := by
  have subset : convexHull ℝ (Set.range modelCorners) ⊆ Metric.closedBall (0 : Space) 1 := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i, rfl⟩
    simp [Metric.mem_closedBall, modelCorner_norm]
  have mem := subset (modelGrid_mem_modelTriangle hq t k)
  simpa only [Metric.mem_closedBall, dist_zero_right] using mem

def modelNormal : Space := EuclideanSpace.basisFun (Fin 3) ℝ 2

theorem modelNormal_unit : ‖modelNormal‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one 2

theorem inner_modelNormal_modelGridCorners {q : ℕ} (t : GridCell q) (k : Fin 3) :
    inner ℝ modelNormal (modelGridCorners t k) = faceHeight := by
  rw [modelNormal, EuclideanSpace.basisFun_inner]
  unfold modelGridCorners TriangleGrid.cellCorners TriangleGrid.point
  change faceHeight + _ * (faceHeight - faceHeight) + _ * (faceHeight - faceHeight) = faceHeight
  ring

theorem norm_sub_modelGridCorners {q : ℕ} (t : GridCell q) {k l : Fin 3} (ne : k ≠ l) :
    ‖modelGridCorners t k - modelGridCorners t l‖ = icosahedronEdge / q := by
  have eu : ‖(q : ℝ)⁻¹ • (cornerB - cornerA)‖ = icosahedronEdge / q := norm_stepU q
  have innerBA := (real_inner_comm cornerA cornerB).trans corner_pair_inner.1
  have eqV : ‖cornerC - cornerA‖ = ‖cornerB - cornerA‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, norm_sub_sq_real, cornerA_unit, cornerB_unit, cornerC_unit,
      corner_pair_inner.2.2, innerBA]
  have eqD : ‖cornerB - cornerC‖ = ‖cornerB - cornerA‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, norm_sub_sq_real, cornerA_unit, cornerB_unit, cornerC_unit,
      corner_pair_inner.2.1, innerBA]
  have ev : ‖(q : ℝ)⁻¹ • (cornerC - cornerA)‖ = icosahedronEdge / q := by
    rw [norm_smul, eqV, ← norm_smul, eu]
  have ed : ‖(q : ℝ)⁻¹ • (cornerB - cornerA) - (q : ℝ)⁻¹ • (cornerC - cornerA)‖ =
      icosahedronEdge / q := by
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, eqD, ← norm_smul, eu]
  exact TriangleGrid.norm_cellCorners_sub cornerA cornerB cornerC q _ _ _ eu ev ed k l ne

theorem map_modelGridCorners {q : ℕ} (t : MeshFace q) (e : Space ≃ₗᵢ[ℝ] Space)
    (he : ∀ k, e (modelCorners k) = unitFaceCorners t.1 k) (k : Fin 3) :
    e (modelGridCorners t.2 k) = radius⁻¹ • chordCorners t k := by
  simp only [modelGridCorners, chordCorners, TriangleGrid.cellCorners, TriangleGrid.point,
    map_add, map_smul, map_sub]
  have h₀ : e cornerA = radius⁻¹ • faceCorners t.1 0 := he 0
  have h₁ : e cornerB = radius⁻¹ • faceCorners t.1 1 := he 1
  have h₂ : e cornerC = radius⁻¹ • faceCorners t.1 2 := he 2
  rw [h₀, h₁, h₂]
  module

/-- Radial normalization commutes with the chosen isometry of a macroface. -/
theorem map_normalize_modelGridCorners {q : ℕ} (t : MeshFace q) (e : Space ≃ₗᵢ[ℝ] Space)
    (he : ∀ k, e (modelCorners k) = unitFaceCorners t.1 k) (k : Fin 3) :
    e (normalize (modelGridCorners t.2 k)) = inscribedCorners t k := by
  have mapped : e (normalize (modelGridCorners t.2 k)) =
      normalize (e (modelGridCorners t.2 k)) := by
    simp only [NormedSpace.normalize, map_smul, LinearIsometryEquiv.norm_map]
  rw [mapped, map_modelGridCorners t e he, normalize_smul_of_pos (inv_pos.mpr radius_pos)]
  rfl

/-- Every fine grid triangle has its normalized model triangle as an isometric copy. -/
theorem exists_modelGrid_isometry {q : ℕ} (t : MeshFace q) :
    ∃ e : Space ≃ₗᵢ[ℝ] Space,
      ∀ k, e (normalize (modelGridCorners t.2 k)) = inscribedCorners t k := by
  obtain ⟨e, he⟩ := exists_modelFace_isometry t.1
  exact ⟨e, map_normalize_modelGridCorners t e he⟩

end Unfoldings.FewestNets.Icosahedron
