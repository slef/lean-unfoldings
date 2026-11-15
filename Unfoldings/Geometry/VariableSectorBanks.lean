module

public import Unfoldings.Geometry.VariableSectorHomeomorph
public import Unfoldings.Cone.SectorFrontier

/-! Exact boundary banks of sectors with continuously varying openings. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

variable (α : ℝ) (first : Real.sin α ≠ 0) (width : ℝ≥0 → ℝ)
  (sine : ∀ r, Real.sin (width r) ≠ 0) (regular : ContinuousOn width (Set.Ioi 0))

@[simp] theorem variableSectorHomeomorph_real (r : ℝ≥0) :
    variableSectorHomeomorph α first width sine regular (r : ℂ) = (r : ℂ) := by
  have radius : ‖(r : ℂ)‖₊ = r := by
    apply NNReal.eq
    simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  have same : sectorChangeLinearEquiv α (width r) first (sine r) (r : ℂ) = (r : ℂ) := by
    simpa only [sectorCombination, zero_smul, add_zero] using
      sectorChangeLinearEquiv_combination α (width r) first (sine r) ((r : ℝ), 0)
  change radialLinearMap (fun s => sectorChangeLinearEquiv α (width s) first (sine s)) (r : ℂ) = _
  rw [radialLinearMap_eq_linear_of_norm _ _ (by rw [radius, same]), radius, same]

/-- The second boundary ray becomes precisely the prescribed radius-dependent bank. -/
theorem variableSectorHomeomorph_upper (r : ℝ≥0) :
    variableSectorHomeomorph α first width sine regular (polarRay α * (r : ℂ)) =
      polarRay (width r) * (r : ℂ) := by
  have radius : ‖polarRay α * (r : ℂ)‖₊ = r := by
    apply NNReal.eq
    simp only [coe_nnnorm, norm_mul, norm_polarRay, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  have same : sectorChangeLinearEquiv α (width r) first (sine r) (polarRay α * (r : ℂ)) =
      polarRay (width r) * (r : ℂ) := by
    simpa only [sectorCombination, Complex.ofReal_zero, zero_add, Complex.real_smul,
      mul_comm] using sectorChangeLinearEquiv_combination α (width r) first (sine r) (0, (r : ℝ))
  change radialLinearMap (fun s => sectorChangeLinearEquiv α (width s) first (sine s))
    (polarRay α * (r : ℂ)) = _
  rw [radialLinearMap_eq_linear_of_norm _ _ (by
    rw [radius, same]
    simp only [norm_mul, norm_polarRay, one_mul]), radius, same]

/-- The variable gap is an actual ambient image of a fixed convex sector. -/
def variableSectorGap : Set ℂ :=
  variableSectorHomeomorph α first width sine regular '' planarSector α

theorem isClosed_variableSectorGap : IsClosed (variableSectorGap α first width sine regular) :=
  (variableSectorHomeomorph α first width sine regular).isClosedMap _
    (isClosed_planarSector α first)

/-- Both banks are exact geometric images, including their common source and unbounded ends. -/
theorem frontier_variableSectorGap :
    frontier (variableSectorGap α first width sine regular) =
      Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => polarRay (width r) * (r : ℂ)) := by
  rw [variableSectorGap, ← (variableSectorHomeomorph α first width sine regular).image_frontier,
    frontier_planarSector α first, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  simp only [Function.comp_def, variableSectorHomeomorph_real, variableSectorHomeomorph_upper]

end Unfoldings
