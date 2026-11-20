module

public import Unfoldings.Polyhedron.GaussianAreaPartition
public import Unfoldings.Polyhedron.SupportingNormals
public import Unfoldings.Geometry.StereographicArea
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! Every nonempty Gaussian cell has an internal open hemisphere center. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open MeasureTheory Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- The spherical portion of the outward normal cone at an original site. -/
def gaussianCell (i : F.hullSites) : Set Space :=
  F.gaussianCone i ∩ Metric.sphere 0 1

theorem mem_gaussianCone_iff_inner_sub {i : F.hullSites} {n : Space} :
    n ∈ F.gaussianCone i ↔ ∀ j : F.hullSites, 0 ≤ inner ℝ ((i : Space) - (j : Space)) n := by
  change (∀ j : F.hullSites, inner ℝ n (j : Space) ≤ inner ℝ n (i : Space)) ↔ _
  simp only [inner_sub_left, real_inner_comm (i : Space) n, sub_nonneg]
  exact forall_congr' fun j => by rw [real_inner_comm (j : Space) n]

theorem isCompact_gaussianCell (i : F.hullSites) : IsCompact (F.gaussianCell i) :=
  (isCompact_sphere (0 : Space) 1).inter_left
    (isClosed_finiteHullNormalCone (fun j : F.hullSites => (j : Space)) i)

theorem solidAngle_gaussianCell (i : F.hullSites) :
    solidAngleMeasure (F.gaussianCell i) = solidAngleMeasure (F.gaussianCone i) :=
  solidAngleMeasure_inter_sphere _

theorem gaussianCell_nonempty (P : F.ConvexBoundary) (i : F.hullSites) :
    (F.gaussianCell i).Nonempty := by
  obtain ⟨⟨f, j⟩, _, point⟩ := Finset.mem_image.mp i.property
  let N := P.supportingNormals
  refine ⟨N.normal f, F.mem_gaussianCone_iff.mpr (fun x hx => ?_), ?_⟩
  · have supports := N.supporting f x hx
    have on_plane := N.on_plane f ((C.triangle f).vertex j)
    rw [inner_sub_right, point] at on_plane
    rw [inner_sub_right] at supports
    linarith only [supports, on_plane]
  · simpa only [Metric.mem_sphere, dist_zero_right] using N.unit f

/-- A ray from a strict interior point to the vertex has positive pairing
with every normal in the spherical cell. -/
theorem inner_pos_of_mem_gaussianCell {i : F.hullSites}
    {p n : Space} (hp : p ∈ interior F.vertexHull) (hn : n ∈ F.gaussianCell i) :
    0 < inner ℝ ((i : Space) - p) n := by
  let f := innerSL ℝ n
  have unit : ‖n‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hn.2
  have fne : f ≠ 0 := by
    intro zero
    have h := DFunLike.congr_fun zero n
    change inner ℝ n n = 0 at h
    simp [unit] at h
  have lt := supporting_functional_lt_on_interior f fne F.vertexHull
    (f i) (F.mem_gaussianCone_iff.mp hn.1) p hp
  change inner ℝ n p < inner ℝ n (i : Space) at lt
  rw [real_inner_comm n ((i : Space) - p), inner_sub_right]
  exact sub_pos.mpr lt

/-- A spherical Gaussian cell can be centered at one of its own points and
then lies strictly inside that point's open hemisphere. -/
theorem exists_gaussianCell_center (P : F.ConvexBoundary) (i : F.hullSites)
    (ne : (F.gaussianCell i).Nonempty) :
    ∃ q ∈ F.gaussianCell i, ∀ z ∈ F.gaussianCell i, 0 < inner ℝ q z := by
  obtain ⟨p, hp⟩ := P.interior_nonempty
  let axis := (i : Space) - p
  let f := innerSL ℝ axis
  obtain ⟨w, hw, min⟩ := (F.isCompact_gaussianCell i).exists_isMinOn ne f.continuous.continuousOn
  let a := f w
  have a_pos : 0 < a := F.inner_pos_of_mem_gaussianCell hp hw
  let H := F.gaussianCone i ∩ {z | a ≤ f z}
  have hcone : Convex ℝ (F.gaussianCone i) := by
    rw [show F.gaussianCone i = ⋂ j : F.hullSites,
        {z | 0 ≤ inner ℝ ((i : Space) - (j : Space)) z} by
      ext z
      simp [F.mem_gaussianCone_iff_inner_sub]]
    exact convex_iInter (fun j =>
      convex_halfSpace_ge (innerSL ℝ ((i : Space) - (j : Space))).toLinearMap.isLinear 0)
  have closed : IsClosed H :=
    (isClosed_finiteHullNormalCone (fun j : F.hullSites => (j : Space)) i).inter
      (isClosed_le continuous_const f.continuous)
  have convex : Convex ℝ H :=
    hcone.inter (convex_halfSpace_ge f.toLinearMap.isLinear a)
  have H_ne : H.Nonempty := ⟨w, hw.1, by
    change a ≤ f w
    exact le_rfl⟩
  obtain ⟨x, hx, nearest⟩ :=
    exists_norm_eq_iInf_of_complete_convex H_ne closed.isComplete convex 0
  have x_ne : x ≠ 0 := by
    intro zero
    have h : a ≤ f x := hx.2
    exact a_pos.not_ge (by simpa [zero] using h)
  have belong : NormedSpace.normalize x ∈ F.gaussianCell i := by
    have hx' : x ∈ F.gaussianCone i := hx.1
    refine ⟨F.mem_gaussianCone_iff_inner_sub.mpr (fun j => ?_), ?_⟩
    · rw [NormedSpace.normalize, real_inner_smul_right]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (F.mem_gaussianCone_iff_inner_sub.mp hx' j)
    · simpa [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x_ne
  refine ⟨NormedSpace.normalize x, belong, ?_⟩
  intro z hz
  have z_in : z ∈ H := ⟨hz.1, isMinOn_iff.mp min z hz⟩
  have bound := (norm_eq_iInf_iff_real_inner_le_zero convex hx).1 nearest z z_in
  rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at bound
  have pos : 0 < inner ℝ x z :=
    (sq_pos_of_pos (norm_pos_iff.mpr x_ne)).trans_le (by linarith)
  rw [NormedSpace.normalize, real_inner_smul_left]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr x_ne)) pos

/-- The planar region cut out by a Gaussian cell's rotated supporting hemispheres. -/
def gaussianChartRegion (i : F.hullSites) (q : Space) : Set Plane :=
  {x | ∀ j : F.hullSites,
    0 ≤ inner ℝ (northFrame q ((i : Space) - j)) (inverseStereographic x)}

/-- A Gaussian cell in its own open hemisphere has a compact convex chart
containing zero. The inverse chart recovers the rotated cell exactly. -/
theorem gaussianChartRegion_properties (i : F.hullSites) {q : Space}
    (hq : q ∈ F.gaussianCell i) (hemisphere : ∀ z ∈ F.gaussianCell i, 0 < inner ℝ q z) :
    IsCompact (F.gaussianChartRegion i q) ∧ Convex ℝ (F.gaussianChartRegion i q) ∧
      (0 : Plane) ∈ F.gaussianChartRegion i q ∧
      F.gaussianChartRegion i q ⊆ Metric.ball 0 1 ∧
      inverseStereographic '' F.gaussianChartRegion i q = northFrame q '' F.gaussianCell i := by
  have q_unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq.2
  let L := northFrame q
  let normal (j : F.hullSites) := L ((i : Space) - j)
  let K := F.gaussianChartRegion i q
  have normal_up (j : F.hullSites) : 0 ≤ normal j 2 := by
    change 0 ≤ northFrame q ((i : Space) - j) 2
    rw [northFrame_height q q_unit, real_inner_comm]
    exact F.mem_gaussianCone_iff_inner_sub.mp hq.1 j
  have map_dot (j : F.hullSites) (z : Space) : inner ℝ (normal j) (L z) =
      inner ℝ ((i : Space) - j) z := L.inner_map_map _ _
  have exact_cell : inverseStereographic '' K = L '' F.gaussianCell i := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z := L.symm (inverseStereographic x)
      have mapped : L z = inverseStereographic x := L.apply_symm_apply _
      refine ⟨z, ⟨F.mem_gaussianCone_iff_inner_sub.mpr (fun j => ?_), ?_⟩, mapped⟩
      · rw [← map_dot j z, mapped]
        exact hx j
      · rw [Metric.mem_sphere, dist_zero_right, L.symm.norm_map, inverseStereographic_unit]
    · rintro ⟨z, hz, rfl⟩
      let u := L z
      have up : 0 < u 2 := by
        change 0 < northFrame q z 2
        rw [northFrame_height q q_unit]
        exact hemisphere z hz
      have unit : ‖u‖ = 1 := by
        rw [L.norm_map]
        simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
      have inv : inverseStereographic (stereographicCoord u) = u :=
        inverseStereographic_stereographicCoord unit (by linarith)
      refine ⟨stereographicCoord u, ?_, inv⟩
      intro j
      rw [inv, map_dot]
      exact F.mem_gaussianCone_iff_inner_sub.mp hz.1 j
  have K_disk : K ⊆ Metric.ball 0 1 := by
    intro x hx
    have present : inverseStereographic x ∈ L '' F.gaussianCell i := by
      rw [← exact_cell]
      exact Set.mem_image_of_mem _ hx
    obtain ⟨z, hz, equal⟩ := present
    have up : 0 < inverseStereographic x 2 := by
      rw [← equal]
      change 0 < northFrame q z 2
      rw [northFrame_height q q_unit]
      exact hemisphere z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact (inverseStereographic_upward_iff x).mp up
  have K_closed : IsClosed K := by
    rw [show K = ⋂ j : F.hullSites, {x | 0 ≤ inner ℝ (normal j) (inverseStereographic x)} by
      ext x
      simp [K, gaussianChartRegion, normal, L]]
    exact isClosed_iInter (fun j => isClosed_le continuous_const
      (continuous_const.inner continuous_inverseStereographic))
  refine ⟨(isCompact_closedBall (0 : Plane) 1).of_isClosed_subset K_closed
    (K_disk.trans Metric.ball_subset_closedBall), convex_inverseStereographic_region normal
    normal_up, ?_, K_disk, exact_cell⟩
  intro j
  rw [inverseStereographic_origin, horizontal_inner, northLift_horizontal,
    northLift_height, inner_zero_right, mul_one, zero_add]
  exact normal_up j

/-- Every nonempty Gaussian cell has a centered compact convex chart. -/
theorem exists_gaussianCell_stereographic_chart (P : F.ConvexBoundary) (i : F.hullSites)
    (ne : (F.gaussianCell i).Nonempty) :
    ∃ q ∈ F.gaussianCell i, ∃ K : Set Plane,
      IsCompact K ∧ Convex ℝ K ∧ (0 : Plane) ∈ K ∧ K ⊆ Metric.ball 0 1 ∧
      inverseStereographic '' K = northFrame q '' F.gaussianCell i := by
  obtain ⟨q, hq, hemisphere⟩ := F.exists_gaussianCell_center P i ne
  exact ⟨q, hq, F.gaussianChartRegion i q, F.gaussianChartRegion_properties i hq hemisphere⟩

end Unfoldings.SpatialFolding
