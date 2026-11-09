module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Convex.Contractible

/-! A unit sphere punctured at any specified point is contractible. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contractible_punctured_unit_sphere (pole : Metric.sphere (0 : E) 1) :
    ContractibleSpace ↥(({pole} : Set (Metric.sphere (0 : E) 1))ᶜ) := by
  have unit : ‖pole.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using pole.property
  let chart := stereographic unit
  have source : chart.source = ({pole} : Set (Metric.sphere (0 : E) 1))ᶜ := rfl
  let H : ↥(({pole} : Set (Metric.sphere (0 : E) 1))ᶜ) ≃ₜ (ℝ ∙ pole.val)ᗮ :=
    (Homeomorph.setCongr source.symm).trans
      (chart.toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _))
  exact H.contractibleSpace

end Unfoldings
