module

public import Unfoldings.Roof.SupportedBankPolarErrors
public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.ComplexFrameLength
public import Unfoldings.Geometry.NextEdgeRadialBlocks
public import Unfoldings.Geometry.RadialChainLength

/-! Actual physical cap comparisons preserve prefix margins against the next intrinsic bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

local notation "physical" => K.folding.projectedBoundaryChain full

open Classical in
/-- A radial prefix remains outward against its actual next rolled bank, with explicit loss. -/
theorem SupportedBankWindowComparisons.next_edge_radial_margin
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) {c γ d : ℝ} (positive : 0 < c)
    (normal : ∀ f, c ≤ K.normal f 2) (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1)
    (radial : (physical).RadialFrom control 0) (initial : 0 < dist control ((physical).vertex 0))
    (margin : ∀ i : Fin (m + 1), γ * (‖(physical).vertex i.castSucc - control‖ *
      ‖(physical).edge i‖) ≤
      inner ℝ ((physical).vertex i.castSucc - control) ((physical).edge i))
    (small : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < d)
    (endpoint_margin : d *
      (‖(physical).vertex (Fin.last m).castSucc - (physical).vertex 0‖ *
        ‖(physical).edge (Fin.last m)‖) ≤
      inner ℝ ((physical).vertex (Fin.last m).castSucc - (physical).vertex 0)
        ((physical).edge (Fin.last m))) :
    let Q := K.framedIntrinsicRoll full
    ((d - radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4))) *
      (‖Q.vertex (Fin.last m).castSucc - Q.vertex 0‖ * ‖Q.edge (Fin.last m)‖) ≤
        inner ℝ (Q.vertex (Fin.last m).castSucc - Q.vertex 0) (Q.edge (Fin.last m)) := by
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
      γ⁻¹ * ‖P.vertex j.castSucc - L control‖ :=
    P.radial_prefix_projectedLength (L control) gamma_positive gamma_small framed_margin j.castSucc
  have framed_length : (P.interval 0 m (by omega)).projectedLength ≤
      γ⁻¹ * ‖P.vertex (Fin.last m).castSucc - P.vertex 0‖ := by
    have bound := (P.interval 0 m (by omega)).radial_projectedLength_le_chord
      (L control) gamma_positive gamma_small
      (P.interval_radial_margin (L control) 0 m (by omega) framed_margin)
    simpa only [PolygonalChain.interval, Nat.zero_add, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Fin.val_zero, Fin.mk_zero] using bound
  have framed_endpoint : d * (‖P.vertex (Fin.last m).castSucc - P.vertex 0‖ *
      ‖P.edge (Fin.last m)‖) ≤
      inner ℝ (P.vertex (Fin.last m).castSucc - P.vertex 0) (P.edge (Fin.last m)) := by
    rw [PolygonalChain.inComplexFrame_edge]
    change d * (‖L ((physical).vertex (Fin.last m).castSucc) -
      L ((physical).vertex 0)‖ * ‖L ((physical).edge (Fin.last m))‖) ≤
      inner ℝ (L ((physical).vertex (Fin.last m).castSucc) - L ((physical).vertex 0))
        (L ((physical).edge (Fin.last m)))
    simpa only [← map_sub, L.norm_map, L.inner_map_map] using endpoint_margin
  exact P.next_edge_radial_margin Q (L control) (K.projectedMetricHeadingError full)
    (fun i => K.projectedMetricStretch (full.point i)) (K.framedIntrinsicRoll_edge_factor full)
    speed nonnegative (inv_nonneg.mpr gamma_positive.le)
    (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
    (fun i => (ratios i).1) (fun i => (ratios i).2) gamma_positive.le gamma_small
    framed_margin framed_prefix (comparisons.polar_error nonnegative L genuine) framed_length
    small framed_endpoint

end Unfoldings.ConvexRoof
