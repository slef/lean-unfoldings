module

public import Unfoldings.FewestNets.IcosahedronRealizedCellPolygon

/-! A checked physical radius bounds the tilt of an entire actual cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real Cap

/-- Gnomonic distance from the north site has radius given by the tangent of the angle. -/
theorem norm_meshGnomonic_eq_tan_angle {u v : Space} (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    (short : angle u v < π / 2) : ‖meshGnomonic u v‖ = tan (angle u v) := by
  let L := Cap.northFrame u
  let z := L (meshGnomonic u v)
  have hv : inner ℝ u v ≠ 0 := by
    rw [inner_eq_cos_angle_of_norm_eq_one uu vu]
    exact (cos_pos_of_mem_Ioo ⟨by linarith [angle_nonneg u v, pi_pos], short⟩).ne'
  have vert : z 2 = 0 :=
    (Cap.northFrame_height u uu _).trans (meshGnomonic_normal_inner uu hv)
  have horiz : ‖Cap.horizontal z‖ = ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have sq := Cap.horizontal_norm_sq z
    rw [vert, zero_pow (by decide : 2 ≠ 0), add_zero] at sq
    exact sq.symm
  calc
    ‖meshGnomonic u v‖ = ‖z‖ := (L.norm_map _).symm
    _ = ‖Cap.centeredSlope u v‖ := by
      rw [centeredSlope_eq_horizontal_meshGnomonic uu]
      exact horiz.symm
    _ = tan (angle u v) := Cap.centeredSlope_norm uu vu short

namespace MeshStarRealization

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

include R in
/-- A local bound on the six or five physical vertex radii applies to every unit normal
in the corresponding closed spherical Voronoi cell. -/
theorem angle_le_of_physicalVertex_radius (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (radius : ∀ k, ‖M.physicalVertex k‖ ≤ tan φ)
    {N : Space} (mem : N ∈ sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a) :
    angle (a : Space) N ≤ φ := by
  let V := R.frame.symm N
  let x := R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N)
  have x_mem : x ∈ convexHull ℝ (Set.range M.physicalVertex) := by
    rw [← R.image_sphericalVoronoiCell_eq_physicalPolygon qbig hq outward]
    exact ⟨N, mem, rfl⟩
  have inside : convexHull ℝ (Set.range M.physicalVertex) ⊆ Metric.closedBall (0 : Plane) (tan φ) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro y ⟨k, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using radius k
  have bound : ‖x‖ ≤ tan φ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using inside x_mem
  have unit : ‖(a : Space)‖ = 1 := meshSites_unit hq a
  have Nu : ‖N‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using mem.2
  have Mu : ‖M.direction‖ = 1 :=
    (R.frame.norm_map _).symm.trans ((congrArg norm R.center).trans unit)
  have Vu : ‖V‖ = 1 := (R.frame.symm.norm_map N).trans Nu
  have dot : inner ℝ M.direction V = inner ℝ N (a : Space) := by
    rw [← R.frame.inner_map_map M.direction V, R.center]
    change inner ℝ (a : Space) (R.frame (R.frame.symm N)) = _
    rw [R.frame.apply_symm_apply, real_inner_comm N (a : Space)]
  have pos := inner_pos_of_mem_meshSphericalCell hq a mem
  have angle_eq : angle M.direction V = angle (a : Space) N := by
    have eq := R.frame.toLinearIsometry.angle_map M.direction V
    change angle (R.frame M.direction) (R.frame (R.frame.symm N)) = _ at eq
    rw [R.center, R.frame.apply_symm_apply] at eq
    exact eq.symm
  have short : angle M.direction V < π / 2 := by
    rw [angle, Real.arccos_lt_pi_div_two, Mu, Vu, one_mul, div_one, dot]
    exact pos
  have chart : x = MeshStar.chartPoint M.direction (meshGnomonic M.direction V) := by
    change MeshStar.chartPoint M.direction
      (R.frame.symm ((inner ℝ N (a : Space))⁻¹ • N) - M.direction) = _
    rw [map_smul, meshGnomonic, dot]
  rw [chart, MeshStar.chartPoint_norm_of_tangent Mu genuine
    (meshGnomonic_normal_inner Mu (dot.trans_ne pos.ne')), norm_meshGnomonic_eq_tan_angle Mu Vu short,
    angle_eq] at bound
  by_contra! greater
  exact (not_lt_of_ge bound) (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two nonnegative
    (angle_eq ▸ short) greater)

include R in
/-- A spatial gnomonic radius check also suffices, with no choice of tangent coordinates. -/
theorem angle_le_of_gnomonicVertex_radius (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (radius : ∀ k, ‖M.gnomonicVertex k‖ ≤ tan φ)
    {N : Space} (mem : N ∈ sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a) :
    angle (a : Space) N ≤ φ := by
  have unit := meshSites_unit hq a
  have Nu : ‖N‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using mem.2
  have pos := inner_pos_of_mem_meshSphericalCell hq a mem
  have short : angle (a : Space) N < π / 2 := by
    rw [angle, Real.arccos_lt_pi_div_two, unit, Nu, one_mul, div_one, real_inner_comm]
    exact pos
  have on_slice := (mem_normalCone_iff_mem_siteIncidentNormalSlice qbig hq a N pos).mp mem.1
  have contained : convexHull ℝ (siteIncidentNormalSlice hq a) ⊆
      Metric.closedBall (a : Space) (tan φ) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨⟨t, present⟩, rfl⟩
    obtain ⟨k, rfl⟩ := R.complete t present
    have eq : R.frame (M.gnomonicVertex k) = rawFacetNormal hq (R.face k) - (a : Space) := by
      rw [M.gnomonicVertex_eq_meshGnomonic_dualDirection k (outward k), ← meshGnomonic_map,
        R.center, ← R.facetNormal_eq hq k (outward k), meshGnomonic,
        ← real_inner_comm (a : Space),
        heightOne_facetNormal_eq_rawFacetNormal qbig hq a _ present]
    simpa only [Metric.mem_closedBall, dist_eq_norm, ← eq, R.frame.norm_map] using radius k
  have bound : ‖meshGnomonic (a : Space) N‖ ≤ tan φ := by
    rw [meshGnomonic, ← real_inner_comm (a : Space)]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using contained on_slice
  rw [norm_meshGnomonic_eq_tan_angle unit Nu short] at bound
  by_contra! greater
  exact not_lt_of_ge bound (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two nonnegative short greater)

end MeshStarRealization
end Unfoldings.FewestNets.Icosahedron
