module

public import Unfoldings.FewestNets.FiniteRouting400FirstData
public import Unfoldings.FewestNets.IcosahedronCertifiedCellRouting
public import Unfoldings.FewestNets.IcosahedronFrequency400Tilt

/-! The first maximum-radius record supplies the physical routing at 83.2067 degrees. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real MeshStar Topology

universe u v

set_option maxRecDepth 8192 in
theorem q400FirstGnomonicRadius_bound (i : Fin 6) :
    ‖q400FirstModel.gnomonicVertex i‖ ≤ tan q400FirstScalar.tilt :=
  MeshStar.Checked.gnomonicVertex_norm_le_tan_of_check certificateDenominator_pos
    q400FirstChecked (by decide +kernel) i

open Classical in
/-- A realizing cell with the first frequency-400 key has a constructed
adaptive forest, retaining its checked physical radius-to-inradius ratio. -/
theorem exists_q400First_rotatedAdaptiveRouting
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {F : SpatialFolding C}
    (P : F.ConvexBoundary) (N : F.SupportingNormals) (g : SpatialRotation)
    {a : meshSites 400} (R : MeshStarRealization a q400FirstModel)
    (label : Face → meshSites 400)
    (chosen : ∀ f, N.normal f ∈ strictVoronoiCone (fun b : meshSites 400 =>
      SpatialRotation.linear g (b : Space)) (label f))
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 83.2067 * π / 180) :
    let hq : (0 : ℕ) < 400 := by decide
    let genuine := face_tangent_firstAxis_ne_zero 400 1 1
    let frame := R.rotatedCertificateNorthFrame hq genuine g
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    let slopes := convexHull ℝ (Set.range q400FirstModel.physicalVertex)
    let compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
    let present : slopes.Nonempty :=
      ⟨q400FirstModel.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
    let ρ := q400FirstModel.maximumRadius
    let radius := ρ * (q400FirstWitness.inradius : ℝ)
    ∃ boundary : (frontier slopes).Nonempty,
      Nonempty (roof.CompatibleAdaptiveRouting {f | roof.normalSlope f ∈ slopes}
        (roof.clippedExtension slopes compact present) boundary
        ((fun x : Plane => ρ • x) '' q400FirstWitness.progressBody) radius
        (cos ((π - q400FirstScalar.visualAngle + q400FirstScalar.projectedAngle 83.2067) / 2))
        q400FirstScalar.margin) ∧
      ∀ x ∈ slopes, ‖x‖ < (q400FirstScalar.lengthConstant : ℝ) * radius := by
  let hq : (0 : ℕ) < 400 := by decide
  let genuine := face_tangent_firstAxis_ne_zero 400 1 1
  let frame := R.rotatedCertificateNorthFrame hq genuine g
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  have qbig : 100 ≤ 400 := by decide
  have key : (1, 1) ∈ faceMeshKeys 400 := mem_faceMeshKeys.mpr (by norm_num)
  have outward (k : Fin 6) : 0 < inner ℝ q400FirstModel.direction (q400FirstModel.dual k) :=
    (q400_face_corner_bounds key k).1
  have no_boundary := (R.upperRoof_admissible_label hq genuine g P N qbig outward label chosen).2
  obtain ⟨valid, _, cot_gap, interior_gap⟩ :=
    q400FirstScalar.bounds_of_check certificateDenominator_pos 83.2067 q400FirstScalar_pass
  have tilt_nonnegative : 0 ≤ (q400FirstScalar.tilt : ℝ) := by exact_mod_cast valid.1.le
  have tilt_small : (q400FirstScalar.tilt : ℝ) < 1 := by exact_mod_cast valid.2.1
  have tilt (x : Space) (member : x ∈ sphericalVoronoiCell
      (fun b : meshSites 400 => (b : Space)) a) : angle (a : Space) x ≤ q400FirstScalar.tilt :=
    R.angle_le_of_gnomonicVertex_radius qbig hq outward tilt_nonnegative
      q400FirstGnomonicRadius_bound member
  have height := R.upperRoof_selected_normalHeight hq genuine g P N qbig outward
    (by linarith only [tilt_small, pi_gt_three] : (q400FirstScalar.tilt : ℝ) ≤ π) tilt
  apply R.exists_compatibleAdaptiveRouting_of_checked_witness hq qbig outward genuine
    (fun k => by fin_cases k <;> decide) roof q400FirstMaximumRadius_pos certificateDenominator_pos
    q400FirstCachedCorner q400FirstCachedNormal q400FirstCachedOffset q400FirstScalar q400FirstWitness
    (by norm_num) valid cot_gap interior_gap q400FirstPass no_boundary
  intro f selected i
  apply q400FirstScalar.projected_cornerAngle_le_of_normalHeight valid roof f
    (height f selected) i
  have h := angles f.val i
  norm_num at h ⊢
  exact h

end Unfoldings.FewestNets.Icosahedron
