module

public import Unfoldings.FewestNets.IcosahedronRealizedCellTilt

/-! The verified whole-cell spherical tilt bounds the actual physical slope polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open Real InnerProductGeometry MeshStar

/-- A spatial angle certificate bounds the Euclidean radius in the model's literal chart. -/
theorem physicalPolygon_norm_le_tan_of_cell_tilt
    {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
    (R : MeshStarRealization a M)
    (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    {φ : ℝ} (small : φ < π / 2)
    (tilt : ∀ N ∈ sphericalVoronoiCell (fun b : meshSites q => (b : Space)) a,
      angle (a : Space) N ≤ φ)
    (p : Plane) (member : p ∈ convexHull ℝ (Set.range M.physicalVertex)) :
    ‖p‖ ≤ tan φ := by
  rw [← R.image_sphericalVoronoiCell_eq_physicalPolygon qbig hq outward] at member
  obtain ⟨N, inside, rfl⟩ := member
  let V := R.frame.symm N
  have Nu : ‖N‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
  have Mu : ‖M.direction‖ = 1 :=
    (R.frame.norm_map _).symm.trans ((congrArg norm R.center).trans (meshSites_unit hq a))
  have Vu : ‖V‖ = 1 := (R.frame.symm.norm_map N).trans Nu
  have dot : inner ℝ M.direction V = inner ℝ N (a : Space) := by
    rw [← R.frame.inner_map_map M.direction V, R.center]
    change inner ℝ (a : Space) (R.frame (R.frame.symm N)) = _
    rw [R.frame.apply_symm_apply, real_inner_comm N (a : Space)]
  have pos := inner_pos_of_mem_meshSphericalCell hq a inside
  have angle_eq : angle M.direction V = angle (a : Space) N := by
    have eq := R.frame.toLinearIsometry.angle_map M.direction V
    change angle (R.frame M.direction) (R.frame (R.frame.symm N)) = _ at eq
    rw [R.center, R.frame.apply_symm_apply] at eq
    exact eq.symm
  have short : angle M.direction V < π / 2 := by
    rw [angle, arccos_lt_pi_div_two, Mu, Vu, one_mul, div_one, dot]
    exact pos
  have chart : R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N) =
      chartPoint M.direction (meshGnomonic M.direction V) := by
    change chartPoint M.direction
      (R.frame.symm ((inner ℝ N (a : Space))⁻¹ • N) - M.direction) = _
    rw [map_smul, meshGnomonic, dot]
  change ‖R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N)‖ ≤ tan φ
  rw [chart, chartPoint_norm_of_tangent Mu genuine
    (meshGnomonic_normal_inner Mu (dot.trans_ne pos.ne')),
    norm_meshGnomonic_eq_tan_angle Mu Vu short, angle_eq]
  rcases (tilt N inside).lt_or_eq with strict | equal
  · exact (tan_lt_tan_of_nonneg_of_lt_pi_div_two (angle_nonneg _ _) small strict).le
  · rw [equal]

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
