module

public import Unfoldings.Geometry.Barycentric
public import Mathlib.Geometry.Euclidean.PerpBisector

/-! Affine equations for genuine bisectors and triangle edge supporting lines. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped RealInnerProductSpace

def bisectorFunction (v w : Plane) : Plane →ᵃ[ℝ] ℝ :=
  (innerₛₗ ℝ (w - v)).toAffineMap -
    AffineMap.const ℝ Plane ⟪w - v, midpoint ℝ v w⟫

theorem bisectorFunction_eq_zero_iff (v w x : Plane) :
    bisectorFunction v w x = 0 ↔ dist x v = dist x w := by
  change ⟪w - v, x⟫ - ⟪w - v, midpoint ℝ v w⟫ = 0 ↔ _
  rw [← inner_sub_right]
  exact (AffineSubspace.mem_perpBisector_iff_inner_eq_zero'
    (c := x) (p₁ := v) (p₂ := w)).symm.trans
    AffineSubspace.mem_perpBisector_iff_dist_eq

theorem bisectorFunction_ne_zero {v w : Plane} (different : v ≠ w) :
    bisectorFunction v w ≠ 0 := by
  intro zero
  have equal : bisectorFunction v w v = 0 := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f v) zero
  have lengths := (bisectorFunction_eq_zero_iff v w v).mp equal
  exact different (dist_eq_zero.mp (by simpa using lengths.symm))

theorem Triangle.coord_ne_zero (T : Triangle) (i : Fin 3) : T.coord i ≠ 0 := by
  intro zero
  have equal := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (T.vertex i)) zero
  simp at equal

theorem affine_comp_equiv_ne_zero (f : Plane →ᵃ[ℝ] ℝ) (nonzero : f ≠ 0)
    (A : Plane ≃ᵃⁱ[ℝ] Plane) : f.comp A.toAffineMap ≠ 0 := by
  intro zero
  apply nonzero
  ext x
  have equal := congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g (A.symm x)) zero
  simpa using equal

end Unfoldings
