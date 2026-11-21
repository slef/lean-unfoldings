module

public import Unfoldings.FewestNets.FiniteProgressRouting100Actual
public import Unfoldings.FewestNets.IcosahedronRotatedUpperRoof
public import Unfoldings.Roof.SharpAngleProjection

/-! The first published record constructs adaptive parents on the actual rotated upper roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real MeshStar Topology

universe u v

/-- The maximum projected input angle certified for the first record. -/
def q100FirstProjectedAngle : ℝ :=
  81 * π / 180 + 2 * arcsin ((1 - cos q100UniformTilt) / (1 + cos q100UniformTilt))

private theorem q100UniformTilt_bounds : q100UniformTilt ∈ Set.Ico (0 : ℝ) (π / 2) := by
  have root : sqrt 5 ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have positive := sqrt_nonneg 5
  unfold q100UniformTilt
  exact ⟨by linarith only [root], by linarith only [positive, pi_gt_three]⟩

private theorem cos_q100UniformTilt_pos : 0 < cos q100UniformTilt :=
  cos_pos_of_mem_Ioo ⟨by linarith only [q100UniformTilt_bounds.1, pi_pos], q100UniformTilt_bounds.2⟩

private theorem q100TiltRatio_nonneg :
    0 ≤ (1 - cos q100UniformTilt) / (1 + cos q100UniformTilt) :=
  div_nonneg (sub_nonneg.mpr (cos_le_one _)) (by linarith only [cos_q100UniformTilt_pos])

private theorem q100TiltRatio_lt_one :
    (1 - cos q100UniformTilt) / (1 + cos q100UniformTilt) < 1 :=
  (div_lt_one (by linarith only [cos_q100UniformTilt_pos])).mpr
    (by linarith only [cos_q100UniformTilt_pos])

private theorem q100FirstProjectedAngle_nonneg : 0 ≤ q100FirstProjectedAngle := by
  unfold q100FirstProjectedAngle
  have h := arcsin_nonneg.mpr q100TiltRatio_nonneg
  positivity

set_option maxRecDepth 8192 in
theorem q100FirstProjectedAngle_lt : q100FirstProjectedAngle < 81.841 * π / 180 := by
  let h := certificateDenominator_pos
  let one : CheckedReal certificateDenominator (1 : ℝ) :=
    (CheckedReal.rat certificateDenominator 1).convert (by simp)
  let two : CheckedReal certificateDenominator (2 : ℝ) :=
    (CheckedReal.rat certificateDenominator 2).convert (by norm_num)
  let c := checkQ100UniformTilt.checkCos h 12
  let ratio := (one.sub c).div h (one.add c)
  let correction := two.mul h (ratio.checkArcsin h q100TiltRatio_nonneg q100TiltRatio_lt_one)
  let allowance := (CheckedReal.rat certificateDenominator (0.841 / 180)).mul h
    (CheckedReal.checkPi certificateDenominator)
  have gap := CheckedReal.lt_of_isLT h correction allowance (by decide +kernel)
  push_cast at gap
  unfold q100FirstProjectedAngle
  linarith only [gap]

open Classical in
/-- For angle bound 81 degrees, the first realized cell has an adaptive
forest on the actual upper roof selected by the admissible labels. -/
theorem exists_q100First_rotatedAdaptiveRouting
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {F : SpatialFolding C}
    (P : F.ConvexBoundary) (N : F.SupportingNormals) (g : SpatialRotation)
    {a : meshSites 100} (R : MeshStarRealization a (face 100 1 1))
    (label : Face → meshSites 100)
    (chosen : ∀ f, N.normal f ∈ strictVoronoiCone (fun b : meshSites 100 =>
      SpatialRotation.linear g (b : Space)) (label f))
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 81 * π / 180) :
    let hq : (0 : ℕ) < 100 := by decide
    let genuine := face_tangent_firstAxis_ne_zero 100 1 1
    let frame := R.rotatedCertificateNorthFrame hq genuine g
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    let M := face 100 1 1
    let slopes := convexHull ℝ (Set.range M.physicalVertex)
    let L := convexHull ℝ (Set.range q100FirstBody)
    let compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
    let present : slopes.Nonempty := ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
    let ρ := M.derivativeRadius 100
    ∃ boundary : (frontier slopes).Nonempty,
      Nonempty (roof.CompatibleAdaptiveRouting {f | roof.normalSlope f ∈ slopes}
        (roof.clippedExtension slopes compact present) boundary ((fun w : Plane => ρ • w) '' L)
        (ρ * (q100FirstInradius : ℝ))
        (cos ((π - 81.841 * π / 180 + q100FirstProjectedAngle) / 2)) 0.0073243) := by
  let hq : (0 : ℕ) < 100 := by decide
  let genuine := face_tangent_firstAxis_ne_zero 100 1 1
  let frame := R.rotatedCertificateNorthFrame hq genuine g
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  have qbig : 100 ≤ 100 := le_rfl
  have key : (1, 1) ∈ faceMeshKeys 100 := mem_faceMeshKeys.mpr (by norm_num)
  have outward (k : Fin 6) : 0 < inner ℝ (face 100 1 1).direction ((face 100 1 1).dual k) :=
    (q100_face_corner_bounds key k).1
  have no_boundary := (R.upperRoof_admissible_label hq genuine g P N qbig outward label chosen).2
  have tilt (x : Space) (member : x ∈ sphericalVoronoiCell
      (fun b : meshSites 100 => (b : Space)) a) : angle (a : Space) x ≤ q100UniformTilt := by
    have unit : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using member.2
    rw [angle_comm]
    exact angle_le_meshTilt_of_mem_normalCone hq unit a member.1
  have height := R.upperRoof_selected_normalHeight hq genuine g P N qbig outward
    (by linarith only [q100UniformTilt_bounds.2, pi_pos] : q100UniformTilt ≤ π) tilt
  apply exists_q100First_compatibleAdaptiveRouting roof R no_boundary q100FirstProjectedAngle_nonneg
    q100FirstProjectedAngle_lt
  intro f selected i
  exact roof.projected_cornerAngle_le_of_normal_height cos_q100UniformTilt_pos f
    (height f selected) i (angles f.val i)

end Unfoldings.FewestNets.Icosahedron
