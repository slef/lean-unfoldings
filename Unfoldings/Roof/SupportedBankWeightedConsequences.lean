module

public import Unfoldings.Roof.SupportedBankWeightedRolling

/-! Weighted physical comparisons control actual intrinsic bank length and radial progress. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

local notation "physical" => K.folding.projectedBoundaryChain full

open Classical in
/-- Local physical comparisons give the original intrinsic roll a mesh-independent length bound. -/
theorem SupportedBankWindowComparisons.length_bound
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) {c B γ : ℝ} (positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2) (constant : 0 ≤ B)
    (gamma_nonnegative : 0 ≤ γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0) (initial : 0 < dist control ((physical).vertex 0))
    (margin : ∀ i : Fin (m + 1), γ * (‖(physical).vertex i.castSucc - control‖ *
      ‖(physical).edge i‖) ≤
      inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i))
    (prefix_bound : ∀ j : Fin (m + 1), ((physical).interval 0 j.val (by omega)).projectedLength ≤
      B * ‖(physical).vertex j.castSucc - control‖)
    (length : (physical).projectedLength ≤
      B * ‖(physical).vertex (Fin.last (m + 1)) - (physical).vertex 0‖)
    (small : radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < 1) :
    (C.boundaryChainRoll full).projectedLength ≤
      (c⁻¹ * B / (1 - radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4))) *
        ‖(C.boundaryChainRoll full).vertex (Fin.last (m + 1)) -
          (C.boundaryChainRoll full).vertex 0‖ := by
  let L := K.projectedBankFrame full
  let P := (physical).inComplexFrame L
  let Q := K.framedIntrinsicRoll full
  let E := radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)
  have chord := comparisons.chord_error nonnegative positive normal constant gamma_nonnegative
    gamma_small radial initial margin prefix_bound length
  have ratios (i : Fin (m + 1)) := K.projectedMetricStretch_bounds positive normal (full.point i)
  have lifted : Q.projectedLength ≤ (c⁻¹ * B) *
      ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ := by
    calc
      _ ≤ c⁻¹ * P.projectedLength := P.heading_speed_length_bound Q
        (K.projectedMetricHeadingError full) (fun i => K.projectedMetricStretch (full.point i))
        (K.framedIntrinsicRoll_edge_factor full) (fun i => zero_le_one.trans (ratios i).1)
        (fun i => (ratios i).2)
      _ = c⁻¹ * (physical).projectedLength := by
        rw [PolygonalChain.inComplexFrame_projectedLength]
      _ ≤ c⁻¹ * (B * ‖(physical).vertex (Fin.last (m + 1)) - (physical).vertex 0‖) :=
        mul_le_mul_of_nonneg_left length (inv_nonneg.mpr positive.le)
      _ = _ := by rw [PolygonalChain.inComplexFrame_norm_sub]; ring
  have estimate := length_constant_of_aligned_chord_error
    (K.projectedMetricHeadingError full (Fin.last m))
    (mul_nonneg (inv_nonneg.mpr positive.le) constant) small chord lifted
  simpa only [Q, K.framedIntrinsicRoll_projectedLength, K.framedIntrinsicRoll_chord_norm]
    using estimate

open Classical in
/-- The original bank roll preserves radial progress with the explicit weighted error loss. -/
theorem SupportedBankWindowComparisons.radial_margin
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) {c B γ : ℝ} (positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2) (constant : 0 ≤ B)
    (gamma_nonnegative : 0 ≤ γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0) (initial : 0 < dist control ((physical).vertex 0))
    (margin : ∀ i : Fin (m + 1), γ * (‖(physical).vertex i.castSucc - control‖ *
      ‖(physical).edge i‖) ≤
      inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i))
    (prefix_bound : ∀ j : Fin (m + 1), ((physical).interval 0 j.val (by omega)).projectedLength ≤
      B * ‖(physical).vertex j.castSucc - control‖)
    (length : (physical).projectedLength ≤
      B * ‖(physical).vertex (Fin.last (m + 1)) - (physical).vertex 0‖)
    {d : ℝ}
    (small : radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d)
    (v : Plane)
    (endpoint : d * (‖(physical).vertex (Fin.last (m + 1)) - (physical).vertex 0‖ * ‖v‖) ≤
      inner ℝ ((physical).vertex (Fin.last (m + 1)) - (physical).vertex 0) v) :
    let E := radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)
    let L := K.projectedBankFrame full
    let Q := K.framedIntrinsicRoll full
    ((d - E) / (1 + E)) * (‖Q.vertex (Fin.last (m + 1)) - Q.vertex 0‖ *
      ‖polarRay (K.projectedMetricHeadingError full (Fin.last m)) * L v‖) ≤
      inner ℝ (Q.vertex (Fin.last (m + 1)) - Q.vertex 0)
        (polarRay (K.projectedMetricHeadingError full (Fin.last m)) * L v) := by
  let L := K.projectedBankFrame full
  let P := (physical).inComplexFrame L
  let E := radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)
  have chord := comparisons.chord_error nonnegative positive normal constant gamma_nonnegative
    gamma_small radial initial margin prefix_bound length
  have ratios := K.projectedMetricStretch_bounds positive normal (full.point 0)
  have speed : 1 ≤ c⁻¹ := ratios.1.trans ratios.2
  have error_nonnegative : 0 ≤ E := radialBlockError_nonneg speed nonnegative constant
    (Real.sqrt_nonneg _) (div_pos Real.pi_pos (by norm_num))
  have framed_endpoint : d * (‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ * ‖L v‖) ≤
      inner ℝ (P.vertex (Fin.last (m + 1)) - P.vertex 0) (L v) := by
    change d * (‖L ((physical).vertex (Fin.last (m + 1))) - L ((physical).vertex 0)‖ * ‖L v‖) ≤
      inner ℝ (L ((physical).vertex (Fin.last (m + 1))) - L ((physical).vertex 0)) (L v)
    rw [← map_sub, L.norm_map, L.norm_map, L.inner_map_map]
    exact endpoint
  exact radial_margin_of_aligned_chord_error
    (K.projectedMetricHeadingError full (Fin.last m)) error_nonnegative small chord framed_endpoint

end Unfoldings.ConvexRoof
