module

public import Unfoldings.FewestNets.IcosahedronCellFrontier
public import Unfoldings.FewestNets.IcosahedronChartGenuine
public import Unfoldings.FewestNets.NormalVoronoi

/-! In certificate coordinates, the actual upper-roof selection is exactly the Voronoi label. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open MeshStar

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M) (hq : 0 < q) (qbig : 100 ≤ q)
  (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
  (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)

include qbig outward in
theorem certificateNorthFrame_slope_mem_iff {N : Space}
    (positive : 0 < inner ℝ N (a : Space)) :
    (R.certificateNorthFrame hq genuine N 2)⁻¹ •
        Cap.horizontal (R.certificateNorthFrame hq genuine N) ∈
      convexHull ℝ (Set.range M.physicalVertex) ↔
    N ∈ finiteHullNormalCone (fun s : meshSites q => (s : Space)) a := by
  let V := R.frame.symm N
  have heq : inner ℝ M.direction V = inner ℝ N (a : Space) := by
    rw [← R.frame.inner_map_map, R.center]
    change inner ℝ (a : Space) (R.frame (R.frame.symm N)) = _
    rw [R.frame.apply_symm_apply, real_inner_comm]
  have at_V : 0 < inner ℝ M.direction V := heq.symm ▸ positive
  have side (k : Fin (n + 1)) := R.bisectorTangent_neighbor_ne_zero hq k
  rw [R.certificateNorthFrame_slope, R.siteChartMap_heightOne_eq_chartPoint,
    R.mem_physicalPolygon_iff_side_le qbig hq outward genuine side,
    R.mem_normalCone_iff_neighbor_le qbig hq positive]
  apply forall_congr'
  intro k
  rw [← R.center]
  have map (x : Space) : inner ℝ N (R.frame x) = inner ℝ (R.frame.symm N) x := by
    rw [← R.frame.inner_map_map (R.frame.symm N) x, R.frame.apply_symm_apply]
  rw [map, map]
  exact chart_bisector_le_iff (R.direction_unit hq) (R.neighborDirection_unit hq k)
    genuine at_V (side k)

include qbig outward in
theorem certificateNorthFrame_slope_mem_interior {N : Space} (unit : ‖N‖ = 1)
    (chosen : N ∈ strictVoronoiCone (fun s : meshSites q => (s : Space)) a) :
    (R.certificateNorthFrame hq genuine N 2)⁻¹ •
        Cap.horizontal (R.certificateNorthFrame hq genuine N) ∈
      interior (convexHull ℝ (Set.range M.physicalVertex)) := by
  have cone : N ∈ finiteHullNormalCone (fun s : meshSites q => (s : Space)) a :=
    interior_subset chosen
  have n_mem : N ∈ sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a :=
    ⟨cone, by simpa only [Metric.mem_sphere, dist_zero_right] using unit⟩
  let p := (R.certificateNorthFrame hq genuine N 2)⁻¹ •
    Cap.horizontal (R.certificateNorthFrame hq genuine N)
  have side (k : Fin (n + 1)) := R.bisectorTangent_neighbor_ne_zero hq k
  let U := ⋂ k : Fin (n + 1), {x : Plane |
    inner ℝ x (M.physicalSideNormal k) < M.physicalSideOffset k}
  have open_U : IsOpen U := isOpen_iInter_of_finite (fun k =>
    isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  have inside : U ⊆ convexHull ℝ (Set.range M.physicalVertex) := by
    intro z hz
    apply (R.mem_physicalPolygon_iff_side_le qbig hq outward genuine side z).mpr
    exact fun k => ((Set.mem_iInter.mp hz k) : _ < _).le
  apply interior_maximal inside open_U
  apply Set.mem_iInter.mpr
  intro k
  let b := siteOfCorner (R.face k) (R.index k 1)
  have center : a = siteOfCorner (R.face k) (R.index k 0) :=
    Subtype.ext ((R.corner_eq k 0).trans R.center).symm
  have neighbor : b ≠ a := by
    rw [center]
    exact (siteOfCorner_injective hq (R.face k)).ne ((R.index k).injective.ne (by decide))
  have nb : (b : Space) = R.frame (M.neighborDirection k) := R.corner_eq k 1
  have strict := (mem_interior_finiteHullNormalCone_iff
    (fun _ _ h => Subtype.ext h) a).mp chosen b neighbor
  rw [nb, ← R.center] at strict
  have strict' : inner ℝ (R.frame.symm N) (M.neighborDirection k) <
      inner ℝ (R.frame.symm N) M.direction := by
    rw [← R.frame.inner_map_map (R.frame.symm N) (M.neighborDirection k),
      ← R.frame.inner_map_map (R.frame.symm N) M.direction, R.frame.apply_symm_apply]
    exact strict
  have height : 0 < inner ℝ M.direction (R.frame.symm N) := by
    rw [← R.frame.inner_map_map, R.center, R.frame.apply_symm_apply, real_inner_comm]
    exact inner_pos_of_mem_meshSphericalCell hq a n_mem
  change inner ℝ p (M.physicalSideNormal k) < M.physicalSideOffset k
  dsimp only [p]
  rw [R.certificateNorthFrame_slope, R.siteChartMap_heightOne_eq_chartPoint]
  exact (chart_bisector_lt_iff (R.direction_unit hq) (R.neighborDirection_unit hq k)
    genuine height (side k)).mpr strict'

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
