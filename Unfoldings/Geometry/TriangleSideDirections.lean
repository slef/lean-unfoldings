module

public import Unfoldings.Convex.PolygonSideDirections
public import Unfoldings.Geometry.Barycentric

/-! The sides of a genuine triangle have the finite support presentation used by the routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

open InnerProductSpace

variable (T : Triangle)

/-- The linear part of a barycentric coordinate, represented by a vector. -/
def coordGradient (i : Fin 3) : Plane :=
  (toDual ℝ Plane).symm (T.coord i).linear.toContinuousLinearMap

theorem inner_coordGradient (i : Fin 3) (p : Plane) :
    inner ℝ (T.coordGradient i) p = T.coord i p - T.coord i 0 := by
  rw [coordGradient, toDual_symm_apply]
  have affine := (T.coord i).map_vadd (0 : Plane) p
  change T.coord i (p + 0) = (T.coord i).linear p + T.coord i 0 at affine
  rw [add_zero] at affine
  change (T.coord i).linear p = T.coord i p - T.coord i 0
  linarith only [affine]

theorem coordGradient_ne_zero (i : Fin 3) : T.coordGradient i ≠ 0 := by
  intro equal
  have first := T.inner_coordGradient i (T.vertex i)
  have last := T.inner_coordGradient i (T.vertex (next i))
  have different : i ≠ next i := by fin_cases i <;> decide
  simp [equal] at first
  rw [equal, inner_zero_left, coord_vertex, ite_eq_right different] at last
  linarith only [first, last]

/-- Outward normals are indexed by the opposite corners. The origin is strictly
inside when the triangle is used as a compact horizontal slope selector. -/
def polygonSideDirections (origin : (0 : Plane) ∈ interior T.carrier) :
    PolygonSideDirections (Fin 3) T.carrier where
  normal i := -NormedSpace.normalize (T.coordGradient i)
  offset i := ‖T.coordGradient i‖⁻¹ * T.coord i 0
  unit i := by
    rw [norm_neg]
    exact NormedSpace.norm_normalize (T.coordGradient_ne_zero i)
  positive i :=
    mul_pos (inv_pos.mpr (norm_pos_iff.mpr (T.coordGradient_ne_zero i)))
      (T.interior_eq_pos_coord.subset origin i)
  carrier_eq := by
    rw [T.carrier_eq_nonneg_coord]
    ext p
    simp only [Set.mem_ofPred_eq]
    have side (i : Fin 3) :
        inner ℝ (-NormedSpace.normalize (T.coordGradient i)) p ≤
          ‖T.coordGradient i‖⁻¹ * T.coord i 0 ↔ 0 ≤ T.coord i p := by
      change inner ℝ (-(‖T.coordGradient i‖⁻¹ • T.coordGradient i)) p ≤ _ ↔ _
      rw [inner_neg_left, real_inner_smul_left, T.inner_coordGradient, ← mul_neg,
        mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr (T.coordGradient_ne_zero i)))]
      constructor <;> intro h <;> linarith only [h]
    exact forall_congr' fun i => (side i).symm

end Unfoldings.Triangle
