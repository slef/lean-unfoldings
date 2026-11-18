module

public import Unfoldings.Roof.SourceStartBankPolarErrors
public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.ComplexFrameSubhistories
public import Unfoldings.Geometry.RadialBlockSubhistories
public import Unfoldings.Geometry.SourceStartRadialPerturbation
public import Unfoldings.Roof.ProjectedBankDirections

/-! Actual local comparisons preserve intrinsic radial margins from the source-starting edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η γ d c : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

local notation "physical" => K.folding.projectedBoundaryChain full

open Classical in
/-- Every intrinsic subhistory retains its margin, including the actual source-starting edge. -/
theorem SupportedBankWindowComparisons.sourceStart_subhistory_margin
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (source : control = (physical).vertex 0)
    (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0)
    (margin : ∀ i : Fin (m + 1), γ *
      (‖(physical).vertex i.castSucc - control‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i))
    (nonnegative : 0 ≤ η) (cos_positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2)
    (all_anchors : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), j.val ≤ i.val →
      d * (‖(physical).vertex i.castSucc - (physical).vertex j‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex j) ((physical).edge i))
    (small : radialBlockError c⁻¹ η γ⁻¹
      (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d)
    (j : Fin (m + 2)) (i : Fin (m + 1)) (earlier : j.val ≤ i.val) :
    ((d - radialBlockError c⁻¹ η γ⁻¹
        (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η γ⁻¹
        (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4))) *
      (‖(C.boundaryChainRoll full).vertex i.castSucc - (C.boundaryChainRoll full).vertex j‖ *
        ‖(C.boundaryChainRoll full).edge i‖) ≤
      inner ℝ ((C.boundaryChainRoll full).vertex i.castSucc - (C.boundaryChainRoll full).vertex j)
        ((C.boundaryChainRoll full).edge i) := by
  let L := K.projectedBankFrame full
  let P := (physical).inComplexFrame L
  let Q := K.framedIntrinsicRoll full
  have radial_at_start : (physical).RadialFrom ((physical).vertex 0) 0 := by
    simpa only [source] using radial
  have genuine (k : Fin (m + 2)) (later : 0 < k.val) :
      (physical).vertex k - control ≠ 0 := by
    rw [source]
    exact (physical).sourceStart_vertex_ne_zero radial_at_start
      (K.projectedBoundaryChain_edge_ne_zero full 0) k later
  have ratios (k) := K.projectedMetricStretch_bounds cos_positive normal (full.point k)
  have speed : 1 ≤ c⁻¹ := (ratios 0).1.trans (ratios 0).2
  have framed_margin (k) : γ * (‖P.vertex k.castSucc - L control‖ * ‖P.edge k‖) ≤
      inner ℝ (P.vertex k.castSucc - L control) (P.edge k) := by
    rw [PolygonalChain.inComplexFrame_radial_inner, PolygonalChain.inComplexFrame_radius,
      PolygonalChain.inComplexFrame_edge, L.norm_map]
    exact margin k
  have framed_anchors (a : Fin (m + 2)) (b : Fin (m + 1)) (before : a.val ≤ b.val) :
      d * (‖P.vertex b.castSucc - P.vertex a‖ * ‖P.edge b‖) ≤
        inner ℝ (P.vertex b.castSucc - P.vertex a) (P.edge b) := by
    rw [PolygonalChain.inComplexFrame_chord_inner, PolygonalChain.inComplexFrame_norm_sub,
      PolygonalChain.inComplexFrame_edge, L.norm_map]
    exact all_anchors a b before
  have estimate := P.radialBlock_subhistory_margin Q (L control)
    (K.projectedMetricHeadingError full) (fun k => K.projectedMetricStretch (full.point k))
    (K.framedIntrinsicRoll_edge_factor full) speed nonnegative
    (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
    (fun k => (ratios k).1) (fun k => (ratios k).2) gamma_positive gamma_small
    framed_margin (comparisons.polar_error_of_positive_vertices nonnegative L genuine)
    framed_anchors small j i earlier
  let rotation := complexRotation (K.projectedBankPhase full)
  have chord : Q.vertex i.castSucc - Q.vertex j =
      rotation ((C.boundaryChainRoll full).vertex i.castSucc -
        (C.boundaryChainRoll full).vertex j) := by
    change polarRay (K.projectedBankPhase full) * (C.boundaryChainRoll full).vertex i.castSucc -
      polarRay (K.projectedBankPhase full) * (C.boundaryChainRoll full).vertex j = _
    rw [← mul_sub]
    rfl
  have next : Q.edge i = rotation ((C.boundaryChainRoll full).edge i) :=
    K.framedIntrinsicRoll_edge full i
  simpa only [chord, next, rotation.norm_map, rotation.inner_map_map] using estimate

end Unfoldings.ConvexRoof
