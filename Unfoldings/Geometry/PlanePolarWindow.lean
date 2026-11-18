module

public import Unfoldings.Geometry.PolarWindowInterval
public import Unfoldings.Geometry.ChainAffineMap

/-! Actual planar radial windows give exactly the polar variation in any orthonormal complex
  frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {N n : ℕ} (P : PolygonalChain Plane N) (L : Plane ≃ₗᵢ[ℝ] ℂ) (source : Plane)

/-- Complex coordinates of the same physical planar polygonal chain. -/
def inComplexFrame : PolygonalChain ℂ N := P.affineMap L.toLinearEquiv.toAffineEquiv.toAffineMap

/-- Discrete polar variation equals the actual source-ray angle sum, even in a reflected frame. -/
theorem interval_internal_angle_sum_in_frame
    (genuine : ∀ i, P.vertex i - source ≠ 0)
    (first : ℕ) (fits : first + (n + 2) ≤ N) :
    (∑ k : Fin n, InnerProductGeometry.angle
      ((P.interval first (n + 2) fits).internalSourceRay source k.castSucc)
      ((P.interval first (n + 2) fits).internalSourceRay source k.succ)) =
      interiorVariation ((P.inComplexFrame L).polarVariation (L source))
        ⟨first, by omega⟩ ⟨first + n + 1, by omega⟩ := by
  let Q := P.inComplexFrame L
  have nonzero (i) : Q.vertex i - L source ≠ 0 := by
    change L (P.vertex i) - L source ≠ 0
    rw [← map_sub]
    exact fun zero => genuine i (L.injective (zero.trans (map_zero L).symm))
  rw [← Q.planarWindow_internal_angle_sum (L source) nonzero first fits]
  apply Finset.sum_congr rfl
  intro k _
  let a : Fin (N + 1) := ⟨first + (k.val + 1), by omega⟩
  let b : Fin (N + 1) := ⟨first + (k.val + 1 + 1), by omega⟩
  let R := Complex.orthonormalBasisOneI.repr
  change InnerProductGeometry.angle (P.vertex a - source) (P.vertex b - source) =
    InnerProductGeometry.angle (R (L (P.vertex a)) - R (L source))
      (R (L (P.vertex b)) - R (L source))
  rw [← map_sub, ← map_sub, ← map_sub, ← map_sub]
  exact (L.toLinearIsometry.angle_map _ _).symm.trans
    (R.toLinearIsometry.angle_map _ _).symm

end Unfoldings.PolygonalChain
