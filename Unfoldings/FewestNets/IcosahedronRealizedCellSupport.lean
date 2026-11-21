module

public import Unfoldings.FewestNets.IcosahedronIncidentSupport
public import Unfoldings.FewestNets.IcosahedronRealizedCellPolygon

/-! The certificate's side inequalities describe the complete actual Voronoi cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open NormedSpace

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

theorem mem_normalCone_iff_neighbor_le (qbig : 100 ≤ q) (hq : 0 < q) {N : Space}
    (upward : 0 < inner ℝ N (a : Space)) :
    N ∈ finiteHullNormalCone (fun b : meshSites q => (b : Space)) a ↔
      ∀ k, inner ℝ N (R.frame (M.neighborDirection k)) ≤ inner ℝ N (a : Space) := by
  constructor
  · intro inside k
    have h := inside (siteOfCorner (R.face k) (R.index k 1))
    change inner ℝ N (inscribedCorners (R.face k) (R.index k 1)) ≤ _ at h
    rwa [R.corner_eq] at h
  · intro side
    apply mem_normalCone_of_incident_triangle_support qbig hq a N upward
    intro t ht j
    obtain ⟨k, rfl⟩ := R.complete t ht
    obtain ⟨i, rfl⟩ := (R.index k).surjective j
    rw [R.corner_eq]
    fin_cases i
    · exact le_of_eq (congrArg (inner ℝ N) R.center)
    · exact side k
    · exact side (k + 1)

include R in
theorem direction_unit (hq : 0 < q) : ‖M.direction‖ = 1 :=
  (R.frame.norm_map _).symm.trans ((congrArg norm R.center).trans (meshSites_unit hq a))

include R in
theorem neighborDirection_unit (hq : 0 < q) (k : Fin (n + 1)) :
    ‖M.neighborDirection k‖ = 1 := by
  rw [← R.frame.norm_map, ← show inscribedCorners (R.face k) (R.index k 1) =
    R.frame (M.neighborDirection k) from R.corner_eq k 1]
  exact meshSites_unit hq (siteOfCorner (R.face k) (R.index k 1))

include R in
/-- Precisely the points satisfying all model side inequalities lie in the
certificate polygon. The halfplanes compare all actual sites via the complete local star. -/
theorem mem_physicalPolygon_iff_side_le (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (side : ∀ k, bisectorTangent M.direction (M.neighborDirection k) ≠ 0) (p : Plane) :
    p ∈ convexHull ℝ (Set.range M.physicalVertex) ↔
      ∀ k, inner ℝ p (M.physicalSideNormal k) ≤ M.physicalSideOffset k := by
  let s := M.direction
  have unit := R.direction_unit hq
  have compare {V : Space} (height : 0 < inner ℝ s V) (k : Fin (n + 1)) :
      inner ℝ (MeshStar.chartPoint s (meshGnomonic s V)) (M.physicalSideNormal k) ≤
        M.physicalSideOffset k ↔
      inner ℝ (R.frame V) (R.frame (M.neighborDirection k)) ≤
        inner ℝ (R.frame V) (a : Space) := by
    rw [← R.center, R.frame.inner_map_map, R.frame.inner_map_map]
    exact MeshStar.chart_bisector_le_iff unit (R.neighborDirection_unit hq k)
      genuine height (side k)
  constructor
  · rw [← R.image_sphericalVoronoiCell_eq_physicalPolygon qbig hq outward]
    rintro ⟨N, mem, rfl⟩ k
    let V := R.frame.symm N
    have eq : inner ℝ s V = inner ℝ N (a : Space) := by
      rw [← R.frame.inner_map_map, R.center, real_inner_comm]
      change inner ℝ (R.frame (R.frame.symm N)) (a : Space) = _
      rw [R.frame.apply_symm_apply]
    have height := inner_pos_of_mem_meshSphericalCell hq a mem
    change inner ℝ (MeshStar.chartPoint s
      (R.frame.symm ((inner ℝ N (a : Space))⁻¹ • N) - s)) _ ≤ _
    rw [map_smul, ← eq, ← meshGnomonic]
    apply (compare (by rwa [eq]) k).mpr
    change inner ℝ (R.frame (R.frame.symm N)) _ ≤ inner ℝ (R.frame (R.frame.symm N)) _
    rw [R.frame.apply_symm_apply]
    exact (R.mem_normalCone_iff_neighbor_le qbig hq height).mp mem.1 k
  · intro all_sides
    let V := MeshStar.chartLift s p
    let x := R.frame V
    have height : inner ℝ x (a : Space) = 1 := by
      rw [← R.center, R.frame.inner_map_map, real_inner_comm]
      exact MeshStar.inner_chartLift unit genuine p
    have upward : 0 < inner ℝ x (a : Space) := height ▸ zero_lt_one
    have cone := (R.mem_normalCone_iff_neighbor_le qbig hq upward).mpr (fun k => by
      have pos : 0 < inner ℝ s V := (MeshStar.inner_chartLift unit genuine p).symm ▸ zero_lt_one
      apply (compare pos k).mp
      have chartV : MeshStar.chartPoint s (meshGnomonic s V) = p :=
        MeshStar.chartPoint_meshGnomonic_chartLift (s := s) unit genuine p
      rw [chartV]
      exact all_sides k)
    have mem := (mem_normalCone_iff_mem_siteIncidentNormalSlice qbig hq a x upward).mp cone
    rw [height, inv_one, one_smul] at mem
    have img : R.siteChartMap x ∈ R.siteChartMap '' convexHull ℝ (siteIncidentNormalSlice hq a) :=
      ⟨x, mem, rfl⟩
    rw [AffineMap.image_convexHull, R.image_siteIncidentNormalSlice_eq qbig hq outward] at img
    have chart : R.siteChartMap x = p := by
      change MeshStar.chartPoint s (R.frame.symm (R.frame V) - s) = p
      rw [R.frame.symm_apply_apply]
      have eq := MeshStar.chartPoint_meshGnomonic_chartLift unit genuine p
      rw [meshGnomonic, MeshStar.inner_chartLift unit genuine, inv_one, one_smul] at eq
      exact eq
    exact chart ▸ img

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
