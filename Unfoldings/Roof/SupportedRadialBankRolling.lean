module

public import Unfoldings.Roof.SupportedBankWeightedConsequences
public import Unfoldings.Geometry.RadialChainLength

/-! A positive physical radial margin derives every length hypothesis in weighted bank rolling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

local notation "physical" => K.folding.projectedBoundaryChain full

open Classical in
/-- Positive radial margins alone supply the original rolled bank's quantitative length bound. -/
theorem SupportedBankWindowComparisons.radial_length_bound
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) {c γ : ℝ} (positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2) (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0) (initial : 0 < dist control ((physical).vertex 0))
    (margin : ∀ i : Fin (m + 1), γ *
      (‖(physical).vertex i.castSucc - control‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i))
    (small : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < 1) :
    (C.boundaryChainRoll full).projectedLength ≤
      (c⁻¹ * γ⁻¹ / (1 - radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4))) *
        ‖(C.boundaryChainRoll full).vertex (Fin.last (m + 1)) -
          (C.boundaryChainRoll full).vertex 0‖ :=
  comparisons.length_bound nonnegative positive normal (inv_nonneg.mpr gamma_positive.le)
    gamma_positive.le gamma_small radial initial margin
    (fun j => (physical).radial_prefix_projectedLength control gamma_positive gamma_small
      margin j.castSucc)
    ((physical).radial_projectedLength_le_chord control gamma_positive gamma_small margin) small

open Classical in
/-- Local physical comparisons and radial progress control the entire original intrinsic chord. -/
theorem SupportedBankWindowComparisons.radial_chord_error
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) {c γ : ℝ} (positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2) (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0) (initial : 0 < dist control ((physical).vertex 0))
    (margin : ∀ i : Fin (m + 1), γ *
      (‖(physical).vertex i.castSucc - control‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i)) :
    let P := (physical).inComplexFrame (K.projectedBankFrame full)
    let Q := K.framedIntrinsicRoll full
    ‖polarRay (-K.projectedMetricHeadingError full (Fin.last m)) *
        (Q.vertex (Fin.last (m + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (m + 1)) - P.vertex 0)‖ ≤
      radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) *
        ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ :=
  comparisons.chord_error nonnegative positive normal (inv_nonneg.mpr gamma_positive.le)
    gamma_positive.le gamma_small radial initial margin
    (fun j => (physical).radial_prefix_projectedLength control gamma_positive gamma_small
      margin j.castSucc)
    ((physical).radial_projectedLength_le_chord control gamma_positive gamma_small margin)

end Unfoldings.ConvexRoof
