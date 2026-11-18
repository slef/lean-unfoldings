module

public import Unfoldings.Geometry.ComplexFrameLength

/-! Orthonormal frames preserve margins from every earlier point to every later edge. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {N : ℕ} (P : PolygonalChain Plane N) (L : Plane ≃ₗᵢ[ℝ] ℂ)

/-- The common orthonormal frame preserves every subhistory's chord-to-edge margin. -/
@[simp] theorem inComplexFrame_chord_inner (i j : Fin (N + 1)) (k : Fin N) :
    inner ℝ ((P.inComplexFrame L).vertex i - (P.inComplexFrame L).vertex j)
      ((P.inComplexFrame L).edge k) = inner ℝ (P.vertex i - P.vertex j) (P.edge k) := by
  rw [P.inComplexFrame_edge]
  change inner ℝ (L (P.vertex i) - L (P.vertex j)) (L (P.edge k)) = _
  rw [← map_sub, L.inner_map_map]

end Unfoldings.PolygonalChain
