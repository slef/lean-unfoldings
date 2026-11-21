module

public import Unfoldings.Polyhedron.GaussianChartArcs
public import Unfoldings.Geometry.StereographicSupport
public import Unfoldings.Combinatorics.CyclicAdjacentRemoval

/-! Projected chords turn by at least the original minimum face angle at every Gaussian corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

include P in
private theorem inner_sub_gaussian_eq_zero_of_link_arc {s : C.Seam}
    {a b : C.Vertex Set.univ} (link : C.seamGraph.IsLink s a b) {z : Space}
    (hz : z ∈ closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face)) :
    inner ℝ ((F.gaussianSiteOfVertex a : Space) - (F.gaussianSiteOfVertex b : Space)) z = 0 := by
  have cell_arc : F.gaussianCell (F.gaussianSiteOfVertex a) ∩
      F.gaussianCell (F.gaussianSiteOfVertex b) =
        closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
    rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · exact P.gaussianCell_inter_seam_eq_normal_arc N s
    · rw [Set.inter_comm]
      exact P.gaussianCell_inter_seam_eq_normal_arc N s
  rw [← cell_arc] at hz
  have left := F.mem_gaussianCone_iff_inner_sub.mp hz.1.1 (F.gaussianSiteOfVertex b)
  have right := F.mem_gaussianCone_iff_inner_sub.mp hz.2.1 (F.gaussianSiteOfVertex a)
  simp only [inner_sub_left] at left right ⊢
  linarith

include P closes covers in
/-- The unsigned turn of the stereographic chords at every genuine normal
vertex is bounded below by the smallest original triangle angle. -/
theorem min_angle_le_of_gaussian_chart_chords
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    (q : Space) (center : q ∈ F.gaussianCell (F.gaussianSiteOfVertex a))
    (strict : q ∈ interior (F.gaussianCone (F.gaussianSiteOfVertex a)))
    (hemisphere : ∀ z ∈ F.gaussianCell (F.gaussianSiteOfVertex a), 0 < inner ℝ q z)
    {eta : ℝ} (positive : 0 < eta) (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i)
    (k : Fin (m + 1)) :
    let p := stereographicCoord ∘ northFrame q ∘ compressedLinkNormal N c count
    let prev := (finRotate (m + 1)).symm k
    let next := finRotate (m + 1) k
    eta ≤ angle (p k - p prev) (p next - p k) := by
  let next := finRotate (m + 1)
  let normal := compressedLinkNormal N c count
  let L := northFrame q
  let p := stereographicCoord ∘ L ∘ normal
  let ai := F.gaussianSiteOfVertex a
  let K := F.gaussianChartRegion ai q
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  have three := P.three_le_count_compressedLinkNormal N c closes covers count extreme
  have q_unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using center.2
  have ⟨pinj, arc_in, _, _⟩ := P.compressedLinkNormal_chart_arcs N c closes covers count
    extreme q center strict hemisphere
  have p_in (i : Fin (m + 1)) : p i ∈ K := by
    apply (F.gaussianChartRegion_properties _ center hemisphere).1.isClosed.frontier_subset
    apply arc_in i
    exact Set.mem_image_of_mem _ (Set.mem_insert _ _)
  have rotate_inv (i : Fin (m + 1)) : inverseStereographic (p i) = L (normal i) := by
    have normal_in : normal i ∈ F.gaussianCell ai := by
      have mem : normal i ∈ Set.range
          (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) := ⟨i, rfl⟩
      rw [range_compressed_linkNormals N c covers count] at mem
      obtain ⟨f, j, at_a, hf⟩ := mem
      rw [← hf]
      exact Eq.mp (congrArg (fun w => N.normal f ∈ F.gaussianCell (F.gaussianSiteOfVertex w)) at_a)
        (F.normal_mem_gaussianCell_of_corner N f j)
    have n_unit : ‖L (normal i)‖ = 1 := by
      rw [L.norm_map]
      simpa only [Metric.mem_sphere, dist_zero_right] using normal_in.2
    have height : -1 < L (normal i) 2 := by
      change -1 < northFrame q (normal i) 2
      rw [northFrame_height q q_unit]
      linarith [hemisphere _ normal_in]
    exact inverseStereographic_stereographicCoord n_unit height
  obtain ⟨b, d, link_b, link_d, angle_bd⟩ :=
    P.min_angle_le_of_adjacent_gaussian_supports
      N c closes covers (show F.toSpace Set.univ (C.vertexPoint Set.univ a) ∈
        F.vertexHull.extremePoints ℝ from extreme) min_angle count k
      (finRotate_ne_of_three_le three k)
  let bdir := L ((ai : Space) - (F.gaussianSiteOfVertex b : Space))
  let ddir := L ((ai : Space) - (F.gaussianSiteOfVertex d : Space))
  have angle_dir : eta ≤ angle bdir ddir :=
    (L.toLinearIsometry.angle_map _ _).symm ▸ angle_bd
  have up {t : C.Vertex Set.univ} {e : C.Seam} (link : C.seamGraph.IsLink e a t) :
      0 < L ((ai : Space) - (F.gaussianSiteOfVertex t : Space)) 2 := by
    have unequal : F.gaussianSiteOfVertex t ≠ ai := by
      change F.gaussianSiteOfVertex t ≠ F.gaussianSiteOfVertex a
      rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
      · exact fun h => gaussianSiteOfVertex_seam_ne (F := F) e (congrArg Subtype.val h.symm)
      · exact fun h => gaussianSiteOfVertex_seam_ne (F := F) e (congrArg Subtype.val h)
    change 0 < northFrame q ((ai : Space) - (F.gaussianSiteOfVertex t : Space)) 2
    rw [northFrame_height q q_unit, inner_sub_right, sub_pos]
    exact (mem_interior_finiteHullNormalCone_iff Subtype.val_injective ai).mp strict _ unequal
  have b_pos : 0 < bdir 2 := up link_b
  have d_pos : 0 < ddir 2 := up link_d
  have b_ne : bdir ≠ 0 := fun h => b_pos.ne' (by rw [h, PiLp.zero_apply])
  have d_ne : ddir ≠ 0 := fun h => d_pos.ne' (by rw [h, PiLp.zero_apply])
  have less_pi : angle bdir ddir < Real.pi := by
    apply lt_of_le_of_ne (angle_le_pi _ _)
    intro eq
    obtain ⟨t, hn, ht⟩ := (angle_eq_pi_iff.mp eq).2
    have hv := congrArg (fun u : Space => u 2) ht
    change ddir 2 = t * bdir 2 at hv
    linarith only [hv, d_pos, mul_neg_of_neg_of_pos hn b_pos]
  have at_b : inner ℝ bdir (inverseStereographic (p k)) = 0 := by
    rw [rotate_inv, show inner ℝ bdir (L (normal k)) = _ from L.inner_map_map _ _]
    apply P.inner_sub_gaussian_eq_zero_of_link_arc N link_b
    rw [(P.compressedLinkNormal_arcEnds N c closes covers count k).closedMinorArc]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have at_d : inner ℝ ddir (inverseStereographic (p k)) = 0 := by
    rw [rotate_inv, show inner ℝ ddir (L (normal k)) = _ from L.inner_map_map _ _]
    apply P.inner_sub_gaussian_eq_zero_of_link_arc N link_d
    have ends := P.compressedLinkNormal_arcEnds N c closes covers count (next k)
    change HasGaussianArcEnds N (s (next k)).val (normal (next.symm (next k))) (normal (next k))
      at ends
    rw [next.symm_apply_apply] at ends
    rw [ends.closedMinorArc]
    exact Set.mem_insert _ _
  have prev_ne : p (next.symm k) ≠ p k := pinj.ne (fun h =>
    finRotate_ne_of_three_le three k ((congrArg next h).symm.trans (next.apply_symm_apply k)))
  have next_ne : p (next k) ≠ p k := pinj.ne (finRotate_ne_of_three_le three k)
  have small := angle_chords_le_pi_sub_spherical_exterior b_ne d_ne prev_ne next_ne
    (positive.trans_le angle_dir) less_pi b_pos.le d_pos.le at_b at_d
    (p_in (next.symm k) (F.gaussianSiteOfVertex b)) (p_in (next.symm k) (F.gaussianSiteOfVertex d))
    (p_in (next k) (F.gaussianSiteOfVertex b)) (p_in (next k) (F.gaussianSiteOfVertex d))
  change eta ≤ angle (p k - p (next.symm k)) (p (next k) - p k)
  rw [show p k - p (next.symm k) = -(p (next.symm k) - p k) by abel, angle_neg_left]
  linarith only [small, angle_dir]

end Unfoldings.SpatialFolding.ConvexBoundary
