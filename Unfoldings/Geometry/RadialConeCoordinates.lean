module

public import Unfoldings.Geometry.RadialTriangleHull
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Linear independence makes a radial triangle cone a closed full-dimensional cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module Set

variable {v : Fin 3 → Space} (independent : LinearIndependent ℝ v)

/-- The three vertices are a basis of their full-dimensional radial cone. -/
def radialTriangleBasis : Basis (Fin 3) ℝ Space :=
  basisOfLinearIndependentOfCardEqFinrank independent (by simp [Space])

theorem coe_radialTriangleBasis : (radialTriangleBasis independent : Fin 3 → Space) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem mem_radialTriangleCone_iff_basis {x : Space} :
    x ∈ radialTriangleCone v ↔ ∀ j, 0 ≤ (radialTriangleBasis independent).equivFun x j := by
  let B := radialTriangleBasis independent
  have e : (B : Fin 3 → Space) = v := coe_radialTriangleBasis independent
  constructor
  · rintro ⟨w, nonnegative, eq⟩
    have hw : B.equivFun.symm w = x := by
      rw [B.equivFun_symm_apply, e, ← eq]
    have at_x := congrArg B.equivFun hw
    rw [B.equivFun.apply_symm_apply] at at_x
    rw [← at_x]
    exact nonnegative
  · intro nonnegative
    exact ⟨B.equivFun x, nonnegative, by rw [← e, B.sum_equivFun]⟩

include independent in
/-- The cone is the preimage of the closed positive orthant. -/
theorem isClosed_radialTriangleCone : IsClosed (radialTriangleCone v) := by
  have eq : radialTriangleCone v =
      ⋂ j : Fin 3, {x | 0 ≤ (radialTriangleBasis independent).equivFun x j} := by
    ext x
    simp only [mem_radialTriangleCone_iff_basis independent, mem_iInter,
      mem_ofPred_eq]
  rw [eq]
  exact isClosed_iInter fun j =>
    isClosed_le continuous_const ((continuous_apply j).comp
      (radialTriangleBasis independent).equivFun.toLinearMap.continuous_of_finiteDimensional)

include independent in
/-- Nonnegative basis coordinates are preserved by convex combinations. -/
theorem convex_radialTriangleCone : Convex ℝ (radialTriangleCone v) := by
  intro x hx y hy a b ha hb _
  apply (mem_radialTriangleCone_iff_basis independent).mpr
  intro j
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha ((mem_radialTriangleCone_iff_basis independent).mp hx j))
    (mul_nonneg hb ((mem_radialTriangleCone_iff_basis independent).mp hy j))

include independent in
/-- Strictly positive basis coordinates exhibit a point in the interior. -/
theorem interior_radialTriangleCone_nonempty : (interior (radialTriangleCone v)).Nonempty := by
  let B := radialTriangleBasis independent
  let U : Set Space := {x | ∀ j, 0 < B.equivFun x j}
  have open_U : IsOpen U := by
    change IsOpen {x : Space | ∀ j : Fin 3, 0 < B.equivFun x j}
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const ((continuous_apply j).comp
        B.equivFun.toLinearMap.continuous_of_finiteDimensional)
  have inside : U ⊆ radialTriangleCone v := by
    intro x hx
    exact (mem_radialTriangleCone_iff_basis independent).mpr (fun j => (hx j).le)
  let z := B.equivFun.symm (fun _ => 1)
  have member : z ∈ U := by
    change ∀ j, 0 < B.equivFun z j
    simp only [z, LinearEquiv.apply_symm_apply, zero_lt_one, implies_true]
  exact ⟨z, interior_maximal inside open_U member⟩

end Unfoldings
