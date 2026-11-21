module

public import Unfoldings.Geometry.GenericRadialLines
public import Unfoldings.Geometry.LinearCoverTraceConvex
public import Mathlib.Topology.LocallyFinite

/-! Local hinge inequalities imply convexity for a finite radial linear cover. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set

/-- If adjoining regions support one another away from finitely many radial
lines, the continuous piecewise-linear gauge is convex on all of space. -/
theorem convexOn_univ_of_radial_linear_cover {I J : Type*} [Finite I] [Finite J]
    (cell : I → Set Space) (closed : ∀ i, IsClosed (cell i))
    (convex : ∀ i, Convex ℝ (cell i)) (cover : ∀ x, ∃ i, x ∈ cell i)
    (f : Space → ℝ) (piece : I → Space →ₗ[ℝ] ℝ) (agree : ∀ i x, x ∈ cell i → f x = piece i x)
    (radial : J → Space)
    (support : ∀ x, (∀ (j : J) (r : ℝ), x ≠ r • radial j) →
      ∀ i j, x ∈ cell i → x ∈ cell j → ∀ z ∈ cell j, piece i z ≤ piece j z) :
    ConvexOn ℝ Set.univ f := by
  have continuous : Continuous f := (locallyFinite_of_finite cell).continuous
    (iUnion_eq_univ_iff.mpr cover) closed (fun i =>
      (piece i).continuous_of_finiteDimensional.continuousOn.congr (agree i))
  refine ⟨convex_univ, fun p _ q _ a b ha hb ab => ?_⟩
  let good : Set Space := {w | ∀ (i : J) (t r : ℝ),
    AffineMap.lineMap (p + w) (q + w) t ≠ r • radial i}
  let target : Set Space := {w | f (a • (p + w) + b • (q + w)) ≤
    a • f (p + w) + b • f (q + w)}
  have target_closed : IsClosed target := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have good_subset : good ⊆ target := by
    intro w hw
    change ∀ (i : J) (t r : ℝ), AffineMap.lineMap (p + w) (q + w) t ≠ r • radial i at hw
    have trace := convexOn_line_of_linear_cover cell closed convex f piece agree (p + w) (q + w)
      (fun x _ => cover x) (fun t _ i j hi hj =>
        support _ (fun k r => hw k t r) i j hi hj)
    have zero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have one : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have bound := trace.2 zero one ha hb ab
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] at bound
    rw [AffineMap.lineMap_apply_module, show 1 - b = a by linarith only [ab]] at bound
    exact bound
  have dense : Dense good := dense_radial_line_translations radial p q
  have closed_covers := closure_minimal good_subset target_closed
  have zero : (0 : Space) ∈ closure good := by rw [dense.closure_eq]; trivial
  have at_zero := closed_covers zero
  simpa only [target, Set.mem_ofPred_eq, add_zero] using at_zero

end Unfoldings
