module

public import Unfoldings.Geometry.PlanePolarWindow
public import Unfoldings.Geometry.PolygonalLength

/-! Complex orthonormal coordinates preserve actual edge lengths and radial geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {N : ℕ} (P : PolygonalChain Plane N) (L : Plane ≃ₗᵢ[ℝ] ℂ)

@[simp] theorem inComplexFrame_edge (i : Fin N) :
    (P.inComplexFrame L).edge i = L (P.edge i) := (map_sub L _ _).symm

@[simp] theorem inComplexFrame_norm_sub (i j : Fin (N + 1)) :
    ‖(P.inComplexFrame L).vertex i - (P.inComplexFrame L).vertex j‖ =
      ‖P.vertex i - P.vertex j‖ := by
  change ‖L (P.vertex i) - L (P.vertex j)‖ = _
  rw [← map_sub, L.norm_map]

@[simp] theorem inComplexFrame_radius (source : Plane) (i : Fin (N + 1)) :
    ‖(P.inComplexFrame L).vertex i - L source‖ = ‖P.vertex i - source‖ := by
  change ‖L (P.vertex i) - L source‖ = _
  rw [← map_sub, L.norm_map]

@[simp] theorem inComplexFrame_projectedLength :
    (P.inComplexFrame L).projectedLength = P.projectedLength := by
  unfold projectedLength
  simp only [P.inComplexFrame_edge L, L.norm_map]

@[simp] theorem inComplexFrame_interval_projectedLength (first length : ℕ)
    (fits : first + length ≤ N) :
    ((P.inComplexFrame L).interval first length fits).projectedLength =
      (P.interval first length fits).projectedLength :=
  (P.interval first length fits).inComplexFrame_projectedLength L

@[simp] theorem inComplexFrame_radial_inner (source : Plane) (i : Fin N) :
    inner ℝ ((P.inComplexFrame L).vertex i.castSucc - L source)
      ((P.inComplexFrame L).edge i) = inner ℝ (P.vertex i.castSucc - source) (P.edge i) := by
  rw [P.inComplexFrame_edge]
  change inner ℝ (L (P.vertex i.castSucc) - L source) (L (P.edge i)) = _
  rw [← map_sub, L.inner_map_map]

end Unfoldings.PolygonalChain
