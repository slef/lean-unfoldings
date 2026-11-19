module

public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.RadialCornerSector

/-! The original rolled left sector equals its retained boundary fan angle. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- A strictly radial rolled bend keeps the unreduced retained fan angle as its left
aperture. Even a weak original full-turn bound suffices, since a full turn would make
the incident forward bearings antiparallel. -/
theorem boundaryChainRoll_left_aperture (k : Fin n) (radial : ℂ)
    (first : 0 < inner ℝ radial ((C.boundaryChainRoll chain).edge k.castSucc))
    (last : 0 < inner ℝ radial ((C.boundaryChainRoll chain).edge k.succ))
    (small : C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) ≤
      2 * Real.pi) :
    radialLeftCornerWidth radial ((C.boundaryChainRoll chain).edge k.castSucc)
      ((C.boundaryChainRoll chain).edge k.succ) =
        C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ)) := by
  let θ := C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))
  let d := (C.boundaryChainRoll chain).edge k.castSucc
  let e := (C.boundaryChainRoll chain).edge k.succ
  have θpos := C.totalAngle_pos retain (C.boundaryEndVertex retain (chain.point k.succ))
  have nonzero := C.boundaryChainRoll_edge_ne_zero chain k.succ
  have normalized : (-d) / (‖-d‖ : ℂ) = polarRay θ * (e / (‖e‖ : ℂ)) := by
    dsimp only [d, e]
    rw [norm_neg, neg_div, C.boundaryChainRoll_normalized_edge,
      C.boundaryChainRoll_normalized_edge]
    have step : C.boundaryChainRollHeading chain k.succ =
        C.boundaryChainRollHeading chain k.castSucc + (Real.pi - θ) :=
      Fin.partialSum_succ _ k
    have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
    rw [step, ← polarRay_add, show θ +
        (C.boundaryChainRollHeading chain k.castSucc + (Real.pi - θ)) =
        C.boundaryChainRollHeading chain k.castSucc + Real.pi by ring,
      polarRay_add, half]
    ring
  have angle := radialLeftCornerWidth_eq_positiveGapAngle radial d e first last
  have strict : θ < 2 * Real.pi := by
    by_contra! bound
    have full : θ = 2 * Real.pi := le_antisymm small bound
    rw [full, show polarRay (2 * Real.pi) = 1 by simp [polarRay], one_mul] at normalized
    have nonzero_norm : e / (‖e‖ : ℂ) ≠ 0 := div_ne_zero nonzero
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))
    have zero_angle : positiveGapAngle e (-d) = 0 := by
      unfold positiveGapAngle initialGapAngle
      rw [normalized, div_self nonzero_norm]
      simp
    have positive := (radialLeftCornerWidth_bounds radial d e first last).1
    rw [angle, zero_angle] at positive
    exact lt_irrefl _ positive
  exact angle.trans (positiveGapAngle_of_normalized_rotation e (-d) nonzero
    θpos strict normalized)

end Unfoldings.TriangleComplex
