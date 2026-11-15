module

public import Unfoldings.Geometry.RadialLinearHomeomorph
public import Unfoldings.Cone.SectorChange

/-! A continuously varying sector opening is the ambient image of one fixed sector. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

variable (α : ℝ) (first : Real.sin α ≠ 0) (width : ℝ≥0 → ℝ)
  (sine : ∀ r, Real.sin (width r) ≠ 0) (regular : ContinuousOn width (Set.Ioi 0))

include regular in
theorem continuousOn_variableSectorLinear :
    ContinuousOn (fun p : ℝ≥0 × ℂ =>
      sectorChangeLinearEquiv α (width p.1) first (sine p.1) p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have angle : ContinuousOn (fun p : ℝ≥0 × ℂ => width p.1) (Set.Ioi 0 ×ˢ Set.univ) :=
    regular.comp continuous_fst.continuousOn (fun _ member => member.1)
  have direction : ContinuousOn (fun p : ℝ≥0 × ℂ => polarRay (width p.1))
      (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuous_subtype_val.comp Circle.exp.continuous).comp_continuousOn angle
  have coordinates : Continuous (fun p : ℝ≥0 × ℂ =>
      (sectorCombinationHomeomorph α first).symm p.2) :=
    (sectorCombinationHomeomorph α first).symm.continuous.comp continuous_snd
  change ContinuousOn (fun p : ℝ≥0 × ℂ =>
    sectorCombination (width p.1) ((sectorCombinationHomeomorph α first).symm p.2)) _
  exact (Complex.continuous_ofReal.comp (continuous_fst.comp coordinates)).continuousOn.add
    ((continuous_snd.comp coordinates).continuousOn.smul direction)

include regular in
theorem continuousOn_variableSectorLinear_symm :
    ContinuousOn (fun p : ℝ≥0 × ℂ =>
      (sectorChangeLinearEquiv α (width p.1) first (sine p.1)).symm p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have angle : ContinuousOn (fun p : ℝ≥0 × ℂ => width p.1) (Set.Ioi 0 ×ˢ Set.univ) :=
    regular.comp continuous_fst.continuousOn (fun _ member => member.1)
  have ratio : ContinuousOn (fun p : ℝ≥0 × ℂ => p.2.im / Real.sin (width p.1))
      (Set.Ioi 0 ×ˢ Set.univ) :=
    (Complex.continuous_im.comp continuous_snd).continuousOn.div
      (Real.continuous_sin.comp_continuousOn angle) (fun p _ => sine p.1)
  have coordinates : ContinuousOn (fun p : ℝ≥0 × ℂ =>
      (p.2.re - p.2.im / Real.sin (width p.1) * Real.cos (width p.1),
        p.2.im / Real.sin (width p.1))) (Set.Ioi 0 ×ˢ Set.univ) :=
    ((Complex.continuous_re.comp continuous_snd).continuousOn.sub
      (ratio.mul (Real.continuous_cos.comp_continuousOn angle))).prodMk ratio
  change ContinuousOn (fun p : ℝ≥0 × ℂ => sectorCombination α
    (p.2.re - p.2.im / Real.sin (width p.1) * Real.cos (width p.1),
      p.2.im / Real.sin (width p.1))) _
  exact (sectorCombinationHomeomorph α first).continuous.comp_continuousOn coordinates

/-- An ambient homeomorphism preserving each source-centered circle, even if the sector width
has no positive lower bound near radius zero. -/
def variableSectorHomeomorph : ℂ ≃ₜ ℂ :=
  radialLinearHomeomorph
    (fun r => sectorChangeLinearEquiv α (width r) first (sine r))
    (continuousOn_variableSectorLinear α first width sine regular)
    (continuousOn_variableSectorLinear_symm α first width sine regular)

@[simp] theorem norm_variableSectorHomeomorph (z : ℂ) :
    ‖variableSectorHomeomorph α first width sine regular z‖ = ‖z‖ := by
  change ‖radialLinearMap
    (fun r => sectorChangeLinearEquiv α (width r) first (sine r)) z‖ = ‖z‖
  exact norm_radialLinearMap _ z

end Unfoldings
