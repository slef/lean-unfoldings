module

public import Unfoldings.Complex.BoundaryChainRolling
public import Unfoldings.Geometry.PositiveGapAngle

/-! Actual boundary-chain rolling computes the complementary geometric bank aperture. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- The canonical chain retains each original edge length. -/
theorem boundaryChainRoll_edge_length (i : Fin (n + 1)) :
    ‖(C.boundaryChainRoll chain).edge i‖ = C.boundaryBankLength (chain.point i) := by
  rw [boundaryChainRoll, PolygonalChain.ofHeadings_edge, norm_mul, norm_polarRay, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (C.boundaryBankLength_pos _)]

/-- No original bank edge collapses under intrinsic rolling, even if distant edges overlap. -/
theorem boundaryChainRoll_edge_ne_zero (i : Fin (n + 1)) :
    (C.boundaryChainRoll chain).edge i ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [C.boundaryChainRoll_edge_length chain i]
  exact (C.boundaryBankLength_pos _).ne'

/-- The normalized bank direction records the original real rolling heading. -/
theorem boundaryChainRoll_normalized_edge (i : Fin (n + 1)) :
    (C.boundaryChainRoll chain).edge i / (‖(C.boundaryChainRoll chain).edge i‖ : ℂ) =
      polarRay (C.boundaryChainRollHeading chain i) := by
  rw [C.boundaryChainRoll_edge_length, boundaryChainRoll, PolygonalChain.ofHeadings_edge]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (C.boundaryBankLength_pos _).ne')

/-- The right-side aperture of a rolled bank bend is the full-turn complement of the
actual original one-sided fan angle. The fan may exceed a half-turn. -/
theorem boundaryChainRoll_complementary_angle (k : Fin n)
    (small : C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) <
      2 * Real.pi) :
    positiveGapAngle (-(C.boundaryChainRoll chain).edge k.castSucc)
      ((C.boundaryChainRoll chain).edge k.succ) =
        2 * Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) := by
  let θ := C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))
  have θpos := C.totalAngle_pos retain (C.boundaryEndVertex retain (chain.point k.succ))
  apply positiveGapAngle_of_normalized_rotation _ _
    (neg_ne_zero.mpr (C.boundaryChainRoll_edge_ne_zero chain k.castSucc))
    (sub_pos.mpr small) (by linarith)
  rw [norm_neg, neg_div, C.boundaryChainRoll_normalized_edge,
    C.boundaryChainRoll_normalized_edge]
  have step : C.boundaryChainRollHeading chain k.succ =
      C.boundaryChainRollHeading chain k.castSucc + (Real.pi - θ) :=
    Fin.partialSum_succ _ k
  have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
  have periodic : polarRay (2 * Real.pi - θ) = polarRay (-θ) := by
    rw [sub_eq_add_neg, polarRay_add]
    simp [polarRay]
  rw [step, polarRay_add, sub_eq_add_neg, polarRay_add, half, periodic]
  ring

end Unfoldings.TriangleComplex
