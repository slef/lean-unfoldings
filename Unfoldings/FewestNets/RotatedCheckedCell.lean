module

public import Unfoldings.FewestNets.CertifiedCellDevelopment
public import Unfoldings.FewestNets.RealizedCellRadius
public import Unfoldings.FewestNets.UpperRoofComponentTransfer

/-! The checked physical cell net descends to an actual component of the input polyhedron. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open Real InnerProductGeometry MeshStar

universe u v

set_option maxHeartbeats 2000000 in
open Classical in
/-- A verified cell certificate constructs a net of the original labeled
component, regardless of the chosen global rotation and the local tangent frame. -/
theorem hasOriginalEdgeNet_rotated_checked_cell
    {q n m D : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
    (R : MeshStarRealization a M) (hq : 0 < q) (qbig : 100 ≤ q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (pred_ne : ∀ k : Fin (n + 1), k ≠ k - 1)
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {F : SpatialFolding C}
    (P : F.ConvexBoundary) (N : F.SupportingNormals) (g : SpatialRotation)
    (label : Face → meshSites q)
    (chosen : ∀ f, N.normal f ∈ strictVoronoiCone (fun b : meshSites q =>
      SpatialRotation.linear g (b : Space)) (label f))
    {ρ : ℝ} (positive : 0 < ρ) (hD : 0 < D)
    (cp : ∀ k, CheckedPlane D (ρ⁻¹ • M.physicalVertex k))
    (cn : ∀ k, CheckedPlane D (M.physicalSideNormal k))
    (co : ∀ k, CheckedReal D (M.physicalSideOffset k / ρ))
    (scalar : DevelopmentScalarRecord) (w : RoutingCellWitness (n + 1) (m + 1)) {target : ℚ}
    (target_nonnegative : 0 ≤ target) (valid : scalar.ValidFor target)
    (cot_gap : 0 < scalar.cotangentGap) (interior_gap : 0 < scalar.interiorMarginGap target)
    (passed : w.check hD cp cn co scalar = true)
    (height_bound : (3 : ℝ) / 4 ≤ cos scalar.tilt)
    (gap : 0 < developmentGaps scalar.tilt scalar.margin scalar.lengthConstant 0)
    (tilt : ∀ x ∈ sphericalVoronoiCell (fun b : meshSites q => (b : Space)) a,
      angle (a : Space) x ≤ scalar.tilt)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ (target : ℝ) * π / 180)
    (seed : Face) (seed_label : label seed = a) :
    C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  let frame := R.rotatedCertificateNorthFrame hq genuine g
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let cell := convexHull ℝ (Set.range M.physicalVertex)
  have data := R.upperRoof_admissible_label hq genuine g P N qbig outward label chosen
  have φlt : (scalar.tilt : ℝ) < 1 := by exact_mod_cast valid.2.1
  have φsmall : (scalar.tilt : ℝ) < π / 2 := by linarith only [φlt, pi_gt_three]
  have radius := R.physicalPolygon_norm_le_tan_of_cell_tilt qbig hq outward genuine φsmall tilt
  have height := R.upperRoof_selected_normalHeight hq genuine g P N qbig outward
    (by linarith only [φsmall, pi_pos] : (scalar.tilt : ℝ) ≤ π) tilt
  have projected (f : normals.UpperFace) (member : roof.normalSlope f ∈ cell) (i : Fin 3) :
      (roof.projectedTriangle f).cornerAngle i ≤ scalar.projectedAngle target :=
    scalar.projected_cornerAngle_le_of_normalHeight valid roof f (height f member) i (angles f.val i)
  have seed_upper (f : Face) (same : label f = a) : 0 < normals.normal f 2 := by
    obtain ⟨up, equal, _⟩ := R.upperRoof_exists_of_strictVoronoiCone hq genuine g P N qbig
      outward f (same ▸ chosen f)
    exact equal ▸ up.property
  let up : normals.UpperFace := ⟨seed, seed_upper seed seed_label⟩
  obtain localNet := R.hasOriginalEdgeNet_of_checked_witness hq qbig outward genuine pred_ne roof
    positive hD cp cn co scalar w target_nonnegative valid cot_gap interior_gap passed height_bound
    gap data.2 radius projected up ((data.1 up).mpr seed_label)
  have original := C.hasOriginalEdgeNet_of_restrictFaces _ _ localNet
  have same := P.upperRoof_selectionComponent_image_eq_labeled_component N label a frame data.1
    seed_upper up seed_label
  exact Eq.mp (congrArg C.HasOriginalEdgeNet same) original

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
