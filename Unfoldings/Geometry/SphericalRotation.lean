module

public import Unfoldings.Geometry.NorthFrame

/-! Spherical convexity is invariant under orthogonal coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem normalize_linearIsometry (R : Space ≃ₗᵢ[ℝ] Space) (z : Space) :
    NormedSpace.normalize (R z) = R (NormedSpace.normalize z) := by
  simp only [NormedSpace.normalize, map_smul, R.norm_map]

namespace SphericalConvex

theorem image {region : Set Space} (convex : SphericalConvex region)
    (R : Space ≃ₗᵢ[ℝ] Space) : SphericalConvex (R '' region) := by
  constructor
  · rintro _ ⟨n, member, rfl⟩
    rw [R.norm_map]
    exact convex.1 n member
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb nonzero
    have nz : a • u + b • v ≠ 0 := by
      intro zero
      apply nonzero
      rw [← map_smul, ← map_smul, ← map_add, zero, map_zero]
    refine ⟨_, convex.2 u hu v hv a b ha hb nz, ?_⟩
    rw [← map_smul, ← map_smul, ← map_add, normalize_linearIsometry]

end SphericalConvex
end Unfoldings
