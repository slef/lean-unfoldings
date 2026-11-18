module

public import Unfoldings.Roof.SupportedBankPolarErrors
public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.ComplexFrameLength
public import Unfoldings.Geometry.LocalRadialBlocks

/-! Actual physical comparisons imply a mesh-independent weighted chord bound for original
  bank rolls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

local notation "physical" => K.folding.projectedBoundaryChain full

open Classical in
/-- Constructed local caps control the complete original bank roll, allowing arbitrary winding. -/
theorem SupportedBankWindowComparisons.chord_error
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
      B * ‖(physical).vertex (Fin.last (m + 1)) - (physical).vertex 0‖) :
    let P := (physical).inComplexFrame (K.projectedBankFrame full)
    let Q := K.framedIntrinsicRoll full
    ‖polarRay (-K.projectedMetricHeadingError full (Fin.last m)) *
        (Q.vertex (Fin.last (m + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (m + 1)) - P.vertex 0)‖ ≤
      radialBlockError c⁻¹ η B (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) *
        ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ := by
  let L := K.projectedBankFrame full
  let P := (physical).inComplexFrame L
  let Q := K.framedIntrinsicRoll full
  have genuine (i) : (physical).vertex i - control ≠ 0 := by
    intro zero
    have lower := radial.dist_vertices_le physical 0 i le_rfl (Fin.zero_le i)
    have contradiction := initial.trans_le lower
    rw [sub_eq_zero.mp zero, dist_self] at contradiction
    exact (lt_irrefl _) contradiction
  have ratios (i) := K.projectedMetricStretch_bounds positive normal (full.point i)
  have speed : 1 ≤ c⁻¹ := (ratios 0).1.trans (ratios 0).2
  have framed_margin (i) : γ * (‖P.vertex i.castSucc - L control‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - L control) (P.edge i) := by
    rw [PolygonalChain.inComplexFrame_radial_inner, PolygonalChain.inComplexFrame_radius,
      PolygonalChain.inComplexFrame_edge, L.norm_map]
    exact margin i
  have framed_prefix (j : Fin (m + 1)) : (P.interval 0 j.val (by omega)).projectedLength ≤
      B * ‖P.vertex j.castSucc - L control‖ := by
    simpa only [P, PolygonalChain.inComplexFrame_interval_projectedLength,
      PolygonalChain.inComplexFrame_radius] using prefix_bound j
  have framed_length : P.projectedLength ≤
      B * ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ := by
    simpa only [P, PolygonalChain.inComplexFrame_projectedLength,
      PolygonalChain.inComplexFrame_norm_sub] using length
  have width : 0 < Real.pi / 4 := div_pos Real.pi_pos (by norm_num)
  apply P.radialBlock_chord_error Q (K.projectedMetricHeadingError full)
    (fun i => K.projectedMetricStretch (full.point i)) (K.framedIntrinsicRoll_edge_factor full)
    (P.polarVariation (L control)) (fun i => ‖P.vertex i.castSucc - L control‖)
    speed nonnegative constant (Real.sqrt_nonneg _) width
    (fun i => (ratios i).1) (fun i => (ratios i).2)
    (P.polarVariation_nonnegative (L control))
  · intro j
    rw [P.earlierLength_eq_interval_length]
    exact framed_prefix j
  · intro j
    exact P.polarVariation_weighted_bound (L control) gamma_nonnegative gamma_small j
      (framed_margin j)
  · intro i
    exact abs_heading_sub_le_weighted_local_budget (K.projectedMetricHeadingError full)
      (P.polarVariation (L control)) nonnegative width
      (P.polarVariation_nonnegative (L control))
      (comparisons.polar_error nonnegative L genuine) (Fin.last m) i (Fin.le_last i)
  · exact framed_length

end Unfoldings.ConvexRoof
