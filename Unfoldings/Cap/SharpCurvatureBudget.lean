module

public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Cap.NorthCapArea
public import Unfoldings.Convex.FiniteNormalFan
public import Unfoldings.Geometry.SharpDevelopmentThreshold

/-! The sharp Gaussian curvature allowance for the entire shallow cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open MeasureTheory Real
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

private theorem sphericalNormalPolygon_subset_finiteHullNormalCone (v : C.Vertex Set.univ) :
    K.sphericalNormalPolygon v ⊆ finiteHullNormalCone
      (fun w => K.folding.toSpace Set.univ (C.vertexPoint Set.univ w)) v := by
  intro N hn w
  obtain ⟨⟨f, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ w
  have support := K.sphericalNormalPolygon_supports hn f
    ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩
  rw [inner_sub_right, sub_nonpos] at support
  change inner ℝ N ((K.folding.place f) ((C.triangle f).vertex i)) ≤
    inner ℝ N (K.folding.toSpace Set.univ (C.vertexPoint Set.univ v))
  exact support

private theorem sphericalNormalPolygon_north_height {c : ℝ} (positive : 0 < c) (c_le : c ≤ 1)
    (height : ∀ f, c ≤ K.normal f 2) (v : C.Vertex Set.univ)
    {N : Space} (member : N ∈ K.sphericalNormalPolygon v) : c ≤ N 2 := by
  obtain ⟨g, inside, rfl⟩ := member
  have g_bound : ‖g‖ ≤ sqrt (1 - c ^ 2) / c := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      K.normalPolygon_subset_disk positive height v inside
  have scale := (le_div_iff₀ positive).mp g_bound
  have cs : 0 ≤ 1 - c ^ 2 := sub_nonneg.mpr (by
    simpa only [one_pow] using pow_le_pow_left₀ positive.le c_le 2)
  have sq := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) positive.le) (sqrt_nonneg _)).mpr scale
  rw [mul_pow, sq_sqrt cs] at sq
  have n_sq := Cap.horizontal_norm_sq (Cap.northLift g)
  rw [Cap.northLift_horizontal, Cap.northLift_height, one_pow] at n_sq
  have bound : c * ‖Cap.northLift g‖ ≤ 1 := by
    apply (sq_le_sq₀ (by positivity) zero_le_one).mp
    rw [mul_pow, n_sq, one_pow]
    nlinarith only [sq]
  have ne := norm_pos_iff.mpr (Cap.northLift_ne_zero g)
  change c ≤ ‖Cap.northLift g‖⁻¹ * 1
  rwa [mul_one, ← one_div, le_div_iff₀ ne]

/-- The Gaussian polygons pack in the literal spherical cap of the tilt bound. -/
theorem totalCurvature_le_shallowDevelopmentCurvature {φ : ℝ} (nonnegative : 0 ≤ φ)
    (small : φ < π / 2) (tilt : K.TiltBound φ) :
    C.totalInteriorAngularDefect Set.univ ≤ shallowDevelopmentCurvature φ := by
  classical
  let pos (v : C.Vertex Set.univ) := K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)
  have inj : Function.Injective pos := by
    intro v w same
    exact K.projectedVertex_injective (congrArg Cap.horizontal same)
  have additivity := measure_biUnion_finset₀ (s := (Finset.univ : Finset (C.Vertex Set.univ)))
    (μ := solidAngleMeasure) (f := K.sphericalNormalPolygon)
    (fun v _ w _ different => (finiteHullNormalCone_aedisjoint pos (inj.ne different)).mono
      (K.sphericalNormalPolygon_subset_finiteHullNormalCone v)
      (K.sphericalNormalPolygon_subset_finiteHullNormalCone w))
    (fun v _ => (K.compact_sphericalNormalPolygon v).measurableSet.nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true] at additivity
  have cos_pos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos], small⟩
  have packed : (⋃ v, K.sphericalNormalPolygon v) ⊆
      {N : Space | N ∈ Metric.sphere 0 1 ∧ cos φ ≤ N 2} := by
    rintro N mem
    obtain ⟨v, member⟩ := Set.mem_iUnion.mp mem
    exact ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using
      (K.sphericalNormalPolygon_unit member).1,
      K.sphericalNormalPolygon_north_height cos_pos (cos_le_one _) tilt v member⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by
    unfold shallowDevelopmentCurvature
    exact mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr (cos_le_one _)))).mp
  rw [shallowDevelopmentCurvature]
  exact K.ofReal_totalCurvature_le_solid_normal_area.trans (additivity.symm.le.trans
    ((measure_mono packed).trans (Cap.solidAngleMeasure_north_cap_le cos_pos (cos_le_one _))))

end Unfoldings.ConvexCap
