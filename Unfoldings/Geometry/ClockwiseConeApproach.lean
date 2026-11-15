module

public import Unfoldings.Geometry.CircularConeApproach

/-! Clockwise source-circle motion realizes the negative original source-relative normal. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

/-- Negative angular motion has the opposite actual source-circle tangent vector. -/
theorem hasDerivAt_sourceRotation_neg_angle (source p : ℂ) :
    HasDerivAt (fun θ => sourceRotation source (-θ) p) (-(Complex.I * (p - source))) 0 := by
  have derivative : HasDerivAt (fun θ => sourceRotation source θ p)
      (Complex.I * (p - source)) (-(0 : ℝ)) := by
    simpa only [neg_zero] using hasDerivAt_sourceRotation_angle source p
  simpa only [Function.comp_def, neg_one_smul] using!
    derivative.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

/-- The clockwise motion enters any homogeneous cone containing its actual tangent. -/
theorem eventually_clockwise_sub_mem_interior_cone (source p : ℂ) {cone : Set ℂ}
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (tangent : -(Complex.I * (p - source)) ∈ interior cone) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), sourceRotation source (-θ) p - p ∈ interior cone := by
  have derivative := hasDerivAt_sourceRotation_neg_angle source p
  have zero : sourceRotation source (-(0 : ℝ)) p = p := by
    simp [sourceRotation_apply, complexRotation_apply]
  have limit := derivative.tendsto_slope_zero_right
  simp only [zero_add, zero] at limit
  have inside := limit.eventually (isOpen_interior.mem_nhds tangent)
  have lower : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  filter_upwards [inside, lower] with θ sample θpos
  exact (mem_interior_smul_iff_of_homogeneous radial _ (inv_pos.mpr θpos)).mp sample

end Unfoldings
