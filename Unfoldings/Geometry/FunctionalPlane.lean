module

public import Unfoldings.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Euclidean coordinates on a functional level plane

A nonzero real functional on three-dimensional Euclidean space has a
two-dimensional kernel. An orthonormal basis of that kernel constructs an
affine isometric placement of the Euclidean plane through any specified
level point, with exactly the desired level plane as its range.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem functionalKernel_finrank (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    Module.finrank ℝ f.toLinearMap.ker = 2 := by
  have linear_nonzero : f.toLinearMap ≠ 0 := by
    intro zero
    apply nonzero
    ext x
    exact congrArg (fun g : Space →ₗ[ℝ] ℝ => g x) zero
  have dimension := Module.Dual.finrank_ker_add_one_of_ne_zero linear_nonzero
  have dim : Module.finrank ℝ f.toLinearMap.ker + 1 = 3 := by
    simpa only [Space, finrank_euclideanSpace_fin] using dimension
  omega

def functionalKernelFrame (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    f.toLinearMap.ker ≃ₗᵢ[ℝ] Plane :=
  ((stdOrthonormalBasis ℝ f.toLinearMap.ker).reindex
    (finCongr (functionalKernel_finrank f nonzero))).repr

def functionalPlanePlacement (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) (q : Space) :
    Plane →ᵃⁱ[ℝ] Space :=
  (AffineIsometryEquiv.vaddConst ℝ q).toAffineIsometry.comp
    (f.toLinearMap.ker.subtypeₗᵢ.comp
      (functionalKernelFrame f nonzero).symm.toLinearIsometry).toAffineIsometry

@[simp] theorem functionalPlanePlacement_apply (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (q : Space) (p : Plane) :
    functionalPlanePlacement f nonzero q p =
      ((functionalKernelFrame f nonzero).symm p).val + q := rfl

@[simp] theorem functionalPlanePlacement_zero (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (q : Space) : functionalPlanePlacement f nonzero q 0 = q := by
  rw [functionalPlanePlacement_apply, map_zero]
  exact zero_add q

theorem functionalPlanePlacement_level (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (x q : Space) (h : ℝ) (level : f (q - x) = h) (p : Plane) :
    f (functionalPlanePlacement f nonzero q p - x) = h := by
  rw [functionalPlanePlacement_apply, add_sub_assoc, map_add]
  have zero : f ((functionalKernelFrame f nonzero).symm p).val = 0 :=
    ((functionalKernelFrame f nonzero).symm p).property
  rw [zero, zero_add]
  exact level

theorem range_functionalPlanePlacement (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (x q : Space) (h : ℝ) (level : f (q - x) = h) :
    Set.range (functionalPlanePlacement f nonzero q) = {z | f (z - x) = h} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact functionalPlanePlacement_level f nonzero x q h level p
  · intro inside
    let u : f.toLinearMap.ker := ⟨z - q, by
      have identity : z - q = (z - x) - (q - x) := by abel
      change f (z - q) = 0
      rw [identity, map_sub, inside, level, sub_self]⟩
    refine ⟨functionalKernelFrame f nonzero u, ?_⟩
    rw [functionalPlanePlacement_apply, LinearIsometryEquiv.symm_apply_apply]
    exact sub_add_cancel z q

end Unfoldings
