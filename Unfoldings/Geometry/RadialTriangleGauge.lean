module

public import Unfoldings.Geometry.RadialConeCoordinates

/-! The radial gauge of one chord triangle in its cone coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module Set
open scoped BigOperators

variable {v : Fin 3 → Space} (independent : LinearIndependent ℝ v)

theorem radialTriangleBasis_eq_corner (i : Fin 3) :
    radialTriangleBasis independent i = v i :=
  congrFun (coe_radialTriangleBasis independent) i

theorem radialTriangleBasis_coord_corner (i j : Fin 3) :
    (radialTriangleBasis independent).coord i (v j) = if i = j then 1 else 0 := by
  rw [← radialTriangleBasis_eq_corner independent j, Basis.coord_apply, Basis.repr_self_apply]
  simp only [eq_comm]

theorem radialTriangleBasis_coord_eq_weight (w : Fin 3 → ℝ) (i : Fin 3) :
    (radialTriangleBasis independent).coord i (∑ k, w k • v k) = w i := by
  simp only [map_sum, map_smul, radialTriangleBasis_coord_corner, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  simp

def radialTriangleGauge : Space →ₗ[ℝ] ℝ := (radialTriangleBasis independent).sumCoords

theorem radialTriangleGauge_corner (i : Fin 3) :
    radialTriangleGauge independent (v i) = 1 := by
  rw [← radialTriangleBasis_eq_corner independent i]
  exact (radialTriangleBasis independent).sumCoords_self_apply i

/-- A plane through the three corners has the gauge's defining values. -/
theorem radialTriangleGauge_unique (L : Space →ₗ[ℝ] ℝ) (unit : ∀ k, L (v k) = 1) :
    radialTriangleGauge independent = L := by
  apply LinearMap.ext_on_range (independent.span_eq_top_of_card_eq_finrank (by simp [Space]))
  intro k
  rw [radialTriangleGauge_corner, unit]

theorem linear_le_gauge_on_radialTriangleCone (L : Space →ₗ[ℝ] ℝ)
    (le : ∀ k, L (v k) ≤ 1) {x : Space} (hx : x ∈ radialTriangleCone v) :
    L x ≤ radialTriangleGauge independent x := by
  obtain ⟨w, nonnegative, eq⟩ := hx
  rw [eq, map_sum, map_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [map_smul, map_smul, radialTriangleGauge_corner, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (le k) (nonnegative k)

end Unfoldings
