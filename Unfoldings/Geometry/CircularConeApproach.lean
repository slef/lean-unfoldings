module

public import Unfoldings.Geometry.SourceRotation
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Topology.Algebra.ConstMulAction

/-! A source-circle tangent inside a geometric cone supplies actual nearby interior points. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

/-- Positive angular motion has the actual source-circle tangent vector. -/
theorem hasDerivAt_sourceRotation_angle (source p : ℂ) :
    HasDerivAt (fun θ => sourceRotation source θ p) (Complex.I * (p - source)) 0 := by
  have linear : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
  have phase : HasDerivAt polarRay Complex.I 0 := by
    simpa [polarRay, Circle.coe_exp] using! linear.cexp
  simpa only [sourceRotation_apply, complexRotation_apply] using
    (phase.mul_const (p - source)).const_add source

/-- Positive scaling preserves the geometric interior of a homogeneous region. -/
theorem mem_interior_smul_iff_of_homogeneous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {cone : Set E}
    (radial : ∀ (v : E) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (v : E) {r : ℝ} (positive : 0 < r) : r • v ∈ interior cone ↔ v ∈ interior cone := by
  let H : E ≃ₜ E := Homeomorph.smulOfNeZero r positive.ne'
  have same : H ⁻¹' cone = cone := Set.ext (fun w => radial w r positive)
  have inside : H ⁻¹' interior cone = interior cone := by rw [H.preimage_interior, same]
  exact Set.ext_iff.mp inside v

/-- The physical circular motion itself enters the cone, without a tangent-chart premise. -/
theorem eventually_circle_sub_mem_interior_cone (source p : ℂ) {cone : Set ℂ}
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (tangent : Complex.I * (p - source) ∈ interior cone) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), sourceRotation source θ p - p ∈ interior cone := by
  have derivative := hasDerivAt_sourceRotation_angle source p
  have zero : sourceRotation source 0 p = p := by
    simp [sourceRotation_apply, complexRotation_apply]
  have limit := derivative.tendsto_slope_zero_right
  simp only [zero_add, zero] at limit
  have inside := limit.eventually (isOpen_interior.mem_nhds tangent)
  have lower : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  filter_upwards [inside, lower] with θ sample θpos
  exact (mem_interior_smul_iff_of_homogeneous radial _ (inv_pos.mpr θpos)).mp sample

end Unfoldings
