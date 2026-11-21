module

public import Unfoldings.FewestNets.IcosahedronRealizedCellSupport
public import Unfoldings.FewestNets.MeshChartSideEquality

/-! Every point on the actual gnomonic cell rim lies on a certificate side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open MeshStar Topology

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

theorem siteChartMap_heightOne_eq_chartPoint (N : Space) :
    R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N) =
      chartPoint M.direction (meshGnomonic M.direction (R.frame.symm N)) := by
  have dot : inner ℝ M.direction (R.frame.symm N) = inner ℝ N (a : Space) := by
    rw [← R.frame.inner_map_map, R.center, R.frame.apply_symm_apply, real_inner_comm]
  change chartPoint M.direction (R.frame.symm ((inner ℝ N (a : Space))⁻¹ • N) - M.direction) = _
  rw [map_smul, meshGnomonic, dot]

include R in
/-- The boundary cover comes from actual normal ties, including cells at
original macroedges and vertices. -/
theorem frontier_physicalPolygon_subset_sides (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (side : ∀ k, bisectorTangent M.direction (M.neighborDirection k) ≠ 0)
    (pred_ne : ∀ k : Fin (n + 1), k ≠ k - 1) :
    frontier (convexHull ℝ (Set.range M.physicalVertex)) ⊆
      ⋃ k : Fin (n + 1), segment ℝ (M.physicalVertex (k - 1)) (M.physicalVertex k) := by
  classical
  let K := convexHull ℝ (Set.range M.physicalVertex)
  intro p on_boundary
  have is_closed : IsClosed K := ((Set.finite_range _).isCompact_convexHull ℝ).isClosed
  have mem : p ∈ K := by
    have h : p ∈ closure K := on_boundary.1
    rwa [is_closed.closure_eq] at h
  have hit : ∃ k, inner ℝ p (M.physicalSideNormal k) = M.physicalSideOffset k := by
    by_contra! miss
    let U := ⋂ k : Fin (n + 1), {x : Plane |
      inner ℝ x (M.physicalSideNormal k) < M.physicalSideOffset k}
    have open_U : IsOpen U := isOpen_iInter_of_finite (fun k =>
      isOpen_lt (continuous_id.inner continuous_const) continuous_const)
    have at_p : p ∈ U := Set.mem_iInter.mpr (fun k =>
      lt_of_le_of_ne ((R.mem_physicalPolygon_iff_side_le qbig hq outward genuine side p).mp mem k)
        (miss k))
    have within : U ⊆ K := by
      intro x inside
      apply (R.mem_physicalPolygon_iff_side_le qbig hq outward genuine side x).mpr
      exact fun k => ((Set.mem_iInter.mp inside k) : _ < _).le
    exact on_boundary.2 (interior_maximal within open_U at_p)
  obtain ⟨k, tied⟩ := hit
  change p ∈ convexHull ℝ (Set.range M.physicalVertex) at mem
  rw [← R.image_sphericalVoronoiCell_eq_physicalPolygon qbig hq outward] at mem
  obtain ⟨N, HN, rfl⟩ := mem
  let V := R.frame.symm N
  have dot : inner ℝ M.direction V = inner ℝ N (a : Space) := by
    rw [← R.frame.inner_map_map, R.center, ← real_inner_comm N]
    change inner ℝ (a : Space) (R.frame (R.frame.symm N)) = _
    rw [R.frame.apply_symm_apply]
  have up : 0 < inner ℝ M.direction V :=
    dot.symm ▸ inner_pos_of_mem_meshSphericalCell hq a HN
  dsimp only at tied
  rw [R.siteChartMap_heightOne_eq_chartPoint] at tied
  have align : inner ℝ V (M.neighborDirection k) = inner ℝ V M.direction :=
    (chart_bisector_eq_iff (R.direction_unit hq) (R.neighborDirection_unit hq k)
      genuine up (side k)).mp tied
  let b := siteOfCorner (R.face k) (R.index k 1)
  let edge := edgeOpposite hq (R.face k) (R.index k 2)
  have center : siteOfCorner (R.face k) (R.index k 0) = a :=
    Subtype.ext ((R.corner_eq k 0).trans R.center)
  have nb : (b : Space) = R.frame (M.neighborDirection k) := R.corner_eq k 1
  have different : a ≠ b := by
    rw [← center]
    exact (siteOfCorner_injective hq (R.face k)).ne ((R.index k).injective.ne (by decide))
  have ha : a ∈ edge.val := by
    rw [← center]
    exact (site_mem_edgeOpposite_iff hq _ _ _).mpr ((R.index k).injective.ne (by decide))
  have hb : b ∈ edge.val :=
    (site_mem_edgeOpposite_iff hq _ _ _).mpr ((R.index k).injective.ne (by decide))
  have eq : inner ℝ N (b : Space) = inner ℝ N (a : Space) := by
    have h := align
    rw [← R.frame.inner_map_map V (M.neighborDirection k),
      ← R.frame.inner_map_map V M.direction, R.center, ← nb] at h
    change inner ℝ (R.frame (R.frame.symm N)) (b : Space) =
      inner ℝ (R.frame (R.frame.symm N)) (a : Space) at h
    simpa only [R.frame.apply_symm_apply] using h
  have b_cone : N ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) b :=
    fun d => (HN.1 d).trans_eq eq.symm
  have unit : ‖N‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using HN.2
  have arc : N ∈ networkEdge (meshEndpoint hq) edge :=
    (tie_iff_mem_meshEdge_arc qbig hq edge a b different ha hb).mp ⟨unit, HN.1, b_cone⟩
  have img : R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N) ∈
      (fun N : Space => R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N)) ''
        networkEdge (meshEndpoint hq) edge := ⟨N, arc, rfl⟩
  rw [R.image_meshSide_eq_segment qbig hq k (pred_ne k) outward,
    segment_symm] at img
  exact Set.mem_iUnion.mpr ⟨k, img⟩

include R in
/-- Positive certificate rescaling preserves the full cyclic side cover. -/
theorem frontier_normalizedPolygon_subset_sides (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (side : ∀ k, bisectorTangent M.direction (M.neighborDirection k) ≠ 0)
    (pred_ne : ∀ k : Fin (n + 1), k ≠ k - 1)
    {r : ℝ} (nonzero : r ≠ 0) :
    frontier (convexHull ℝ (Set.range (fun k => r⁻¹ • M.physicalVertex k))) ⊆
      ⋃ k : Fin (n + 1), segment ℝ (r⁻¹ • M.physicalVertex (k - 1))
        (r⁻¹ • M.physicalVertex k) := by
  let scale : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero nonzero)
  let L : Plane →ₗ[ℝ] Plane := r⁻¹ • LinearMap.id
  have chart : convexHull ℝ (Set.range (fun k => r⁻¹ • M.physicalVertex k)) =
      scale '' convexHull ℝ (Set.range M.physicalVertex) := by
    change _ = L '' convexHull ℝ (Set.range M.physicalVertex)
    rw [L.image_convexHull, ← Set.range_comp]
    rfl
  intro p hp
  rw [chart, ← scale.image_frontier] at hp
  obtain ⟨x, on_rim, rfl⟩ := hp
  obtain ⟨k, on_side⟩ := Set.mem_iUnion.mp
    (R.frontier_physicalPolygon_subset_sides qbig hq outward genuine side pred_ne on_rim)
  have exact_side : L x ∈ L.toAffineMap '' segment ℝ (M.physicalVertex (k - 1))
      (M.physicalVertex k) := ⟨x, on_side, rfl⟩
  rw [image_segment] at exact_side
  exact Set.mem_iUnion.mpr ⟨k, exact_side⟩

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
