module

public import Unfoldings.Geometry.RadialBody

/-! Continuous radial retraction to the boundary of a compact strictly radial body. -/

@[expose] public section

noncomputable section

namespace Unfoldings.RadialBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : RadialBody E)

def puncturedDirection (x : {x : E // x ≠ 0}) : Metric.sphere (0 : E) 1 :=
  ⟨‖x.val‖⁻¹ • x.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr x.property⟩

theorem continuous_puncturedDirection : Continuous (puncturedDirection (E := E)) :=
  ((continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
    continuous_subtype_val).subtype_mk _

def retractToBoundary (x : {x : E // x ≠ 0}) : frontier B.carrier :=
  B.boundaryHomeomorph.symm (puncturedDirection x)

theorem continuous_retractToBoundary : Continuous B.retractToBoundary :=
  B.boundaryHomeomorph.symm.continuous.comp continuous_puncturedDirection

theorem retractToBoundary_boundary (x : frontier B.carrier) :
    B.retractToBoundary ⟨x.val, B.boundary_ne_zero x⟩ = x :=
  B.boundaryHomeomorph.symm_apply_apply x

end Unfoldings.RadialBody
