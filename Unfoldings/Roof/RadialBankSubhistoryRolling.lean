module

public import Unfoldings.Roof.RadialBankComparisons
public import Unfoldings.Roof.SupportedBankPolarErrors
public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.ComplexFrameSubhistories
public import Unfoldings.Geometry.RadialBlockSubhistories

/-! Constructed physical comparisons preserve radial order on the full original intrinsic roll. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.RadialBankComparisons

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η γ d c : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane} (data : K.RadialBankComparisons φ η γ retain full control)

local notation "physical" => K.folding.projectedBoundaryChain full

include data in
open Classical in
/-- Every earlier actual anchor retains a quantitative margin against every later intrinsic bank. -/
theorem subhistory_margin (nonnegative : 0 ≤ η) (cos_positive : 0 < c)
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
  have genuine (k) : (physical).vertex k - control ≠ 0 := by
    intro zero
    have lower := data.radial.dist_vertices_le physical 0 k le_rfl (Fin.zero_le k)
    have contradiction := data.initial.trans_le lower
    rw [sub_eq_zero.mp zero, dist_self] at contradiction
    exact (lt_irrefl _) contradiction
  have ratios (k) := K.projectedMetricStretch_bounds cos_positive normal (full.point k)
  have speed : 1 ≤ c⁻¹ := (ratios 0).1.trans (ratios 0).2
  have framed_margin (k) : γ * (‖P.vertex k.castSucc - L control‖ * ‖P.edge k‖) ≤
      inner ℝ (P.vertex k.castSucc - L control) (P.edge k) := by
    rw [PolygonalChain.inComplexFrame_radial_inner, PolygonalChain.inComplexFrame_radius,
      PolygonalChain.inComplexFrame_edge, L.norm_map]
    exact data.margin k
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
    (fun k => (ratios k).1) (fun k => (ratios k).2) data.gamma_positive data.gamma_small
    framed_margin (data.windows.polar_error nonnegative L genuine) framed_anchors small j i earlier
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

include data in
/-- Positive remaining margin gives outward tests at every original bank vertex. -/
theorem outward (nonnegative : 0 ≤ η) (cos_positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2)
    (all_anchors : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), j.val ≤ i.val →
      d * (‖(physical).vertex i.castSucc - (physical).vertex j‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex j) ((physical).edge i))
    (small : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d) :
    (C.boundaryChainRoll full).Outward := by
  have ratios := K.projectedMetricStretch_bounds cos_positive normal (full.point 0)
  have speed : 1 ≤ c⁻¹ := ratios.1.trans ratios.2
  have error_nonnegative := radialBlockError_nonneg speed nonnegative
    (inv_nonneg.mpr data.gamma_positive.le) (Real.sqrt_nonneg (1 - γ ^ 2))
    (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
  have loss_nonnegative : 0 ≤
      (d - radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) :=
    div_nonneg (sub_nonneg.mpr small.le) (by positivity)
  intro j i earlier
  have estimate := data.subhistory_margin nonnegative cos_positive normal all_anchors small
    j i earlier
  exact (mul_nonneg loss_nonnegative
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate

include data in
/-- The full intrinsic roll has radial order from all earlier points, including edge interiors. -/
theorem globallyRadiallyMonotone (nonnegative : 0 ≤ η) (cos_positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2)
    (all_anchors : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), j.val ≤ i.val →
      d * (‖(physical).vertex i.castSucc - (physical).vertex j‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex j) ((physical).edge i))
    (small : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d) :
    (C.boundaryChainRoll full).GloballyRadiallyMonotone :=
  PolygonalChain.Outward.globallyRadiallyMonotone _
    (data.outward nonnegative cos_positive normal all_anchors small)

end Unfoldings.ConvexRoof.RadialBankComparisons
