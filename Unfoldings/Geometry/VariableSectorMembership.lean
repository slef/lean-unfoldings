module

public import Unfoldings.Geometry.VariableSectorBanks

/-! Exact pointwise geometric membership in a variable-opening sector. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Positive scaling preserves the actual geometric sector at every opening angle. -/
theorem smul_mem_planarSector_iff (α : ℝ) (z : ℂ) {t : ℝ} (positive : 0 < t) :
    t • z ∈ planarSector α ↔ z ∈ planarSector α := by
  have scale (z : ℂ) (t : ℝ) (nonnegative : 0 ≤ t) (inside : z ∈ planarSector α) :
      t • z ∈ planarSector α := by
    obtain ⟨c, hc, d, hd, equal⟩ := inside
    refine ⟨t * c, mul_nonneg nonnegative hc, t * d, mul_nonneg nonnegative hd, ?_⟩
    simp only [equal, Complex.real_smul, Complex.ofReal_mul]
    ring
  constructor
  · intro inside
    have divided := scale (t • z) t⁻¹ (inv_nonneg.mpr positive.le) inside
    simpa only [smul_smul, inv_mul_cancel₀ positive.ne', one_smul] using divided
  · exact scale z t positive.le

variable (α : ℝ) (first : Real.sin α ≠ 0) (width : ℝ≥0 → ℝ)
  (sine : ∀ r, Real.sin (width r) ≠ 0) (regular : ContinuousOn width (Set.Ioi 0))

/-- At its own radius the ambient variable map has exactly the prescribed geometric opening. -/
theorem variableSectorHomeomorph_mem_sector_iff (z : ℂ) :
    variableSectorHomeomorph α first width sine regular z ∈ planarSector (width ‖z‖₊) ↔
      z ∈ planarSector α := by
  by_cases zero : z = 0
  · subst z
    have origin (angle : ℝ) : (0 : ℂ) ∈ planarSector angle :=
      ⟨0, le_rfl, 0, le_rfl, by simp⟩
    simp only [variableSectorHomeomorph, radialLinearHomeomorph_apply, norm_zero, zero_smul,
      origin]
  · have image_nonzero : sectorChangeLinearEquiv α (width ‖z‖₊) first (sine ‖z‖₊) z ≠ 0 := by
      simpa only [map_zero] using
        (sectorChangeLinearEquiv α (width ‖z‖₊) first (sine ‖z‖₊)).injective.ne zero
    change ‖z‖ • NormedSpace.normalize
      (sectorChangeLinearEquiv α (width ‖z‖₊) first (sine ‖z‖₊) z) ∈
        planarSector (width ‖z‖₊) ↔ z ∈ planarSector α
    rw [smul_mem_planarSector_iff _ _ (norm_pos_iff.mpr zero), NormedSpace.normalize,
      smul_mem_planarSector_iff _ _ (inv_pos.mpr (norm_pos_iff.mpr image_nonzero))]
    exact sectorChangeLinearEquiv_mem_iff α (width ‖z‖₊) first (sine ‖z‖₊) z

/-- Membership is in the actual fixed-angle sector at the point's own radius. -/
theorem mem_variableSectorGap_iff (z : ℂ) :
    z ∈ variableSectorGap α first width sine regular ↔ z ∈ planarSector (width ‖z‖₊) := by
  constructor
  · rintro ⟨w, member, rfl⟩
    have radius : ‖variableSectorHomeomorph α first width sine regular w‖₊ = ‖w‖₊ :=
      NNReal.eq (norm_variableSectorHomeomorph α first width sine regular w)
    rw [radius]
    exact (variableSectorHomeomorph_mem_sector_iff α first width sine regular w).mpr member
  · intro member
    let H := variableSectorHomeomorph α first width sine regular
    have radius : ‖H.symm z‖₊ = ‖z‖₊ := by
      have same := norm_variableSectorHomeomorph α first width sine regular (H.symm z)
      change ‖H (H.symm z)‖ = ‖H.symm z‖ at same
      rw [H.apply_symm_apply] at same
      exact NNReal.eq same.symm
    refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
    apply (variableSectorHomeomorph_mem_sector_iff α first width sine regular _).mp
    change H (H.symm z) ∈ planarSector (width ‖H.symm z‖₊)
    rwa [H.apply_symm_apply, radius]

end Unfoldings
