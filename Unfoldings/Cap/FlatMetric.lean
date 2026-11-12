module

public import Unfoldings.Cap.Flat
public import Unfoldings.Cap.Metric

/-! The uncut flat cap development preserves the entire intrinsic metric. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem flatDevelopment_isometry (flat : K.TiltBound 0) :
    Isometry (K.flatDevelopment flat).toPlane := by
  have height : ∀ f, (1 : ℝ) ≤ K.normal f 2 := fun f => (K.normal_height_eq_one flat f).ge
  have lower : AntilipschitzWith 1 K.toFootprint := by
    have coefficient : (⟨(1 : ℝ)⁻¹, inv_nonneg.mpr zero_le_one⟩ : NNReal) = 1 := by
      ext
      norm_num
    have bound := K.projection_antilipschitz zero_lt_one height
    rw [coefficient] at bound
    exact bound
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (K.flatDevelopment flat).toPlane_lipschitz.edist_le_mul x y
  · rw [K.flatDevelopment_toPlane flat x, K.flatDevelopment_toPlane flat y]
    simpa only [ENNReal.coe_one, one_mul, Subtype.edist_eq, toFootprint] using lower x y

end Unfoldings.ConvexCap
