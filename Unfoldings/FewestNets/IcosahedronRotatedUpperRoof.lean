module

public import Unfoldings.FewestNets.IcosahedronSelectedRoof
public import Unfoldings.Geometry.SpatialRotationAction
public import Unfoldings.Polyhedron.Rotation
public import Unfoldings.Polyhedron.UpperRoof
public import Unfoldings.Roof.GradientSelection

/-! The original upward triangles of a rotated Voronoi cell are selected
by membership in the certificate's exact slope polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open MeshStar SpatialRotation

universe u v

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M) (hq : 0 < q)
  (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
  (g : SpatialRotation)

def rotatedCertificateNorthFrame : Space ≃ₗᵢ[ℝ] Space :=
  (SpatialRotation.isometry g).symm.trans (R.certificateNorthFrame hq genuine)

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem norm_unrotate (x : Space) : ‖linear g⁻¹ x‖ = ‖x‖ :=
  (SpatialRotation.isometry g).symm.norm_map x

private theorem inner_unrotate (x y : Space) :
    inner ℝ (linear g⁻¹ x) y = inner ℝ x (linear g y) := by
  change inner ℝ ((SpatialRotation.isometry g).symm x) y = inner ℝ x ((SpatialRotation.isometry g) y)
  rw [← (SpatialRotation.isometry g).inner_map_map ((SpatialRotation.isometry g).symm x) y, (SpatialRotation.isometry g).apply_symm_apply]

private theorem unrotate_mem_VoronoiCone (strict : Bool) (x : Space) :
    (linear g⁻¹ x ∈ if strict then strictVoronoiCone (fun b : meshSites q => (b : Space)) a
      else finiteHullNormalCone (fun b : meshSites q => (b : Space)) a) ↔
    x ∈ if strict then strictVoronoiCone (fun b : meshSites q => linear g (b : Space)) a
      else finiteHullNormalCone (fun b : meshSites q => linear g (b : Space)) a := by
  have injective : Function.Injective (fun b : meshSites q => (b : Space)) :=
    fun _ _ h => Subtype.ext h
  have rotated : Function.Injective (fun b : meshSites q => linear g (b : Space)) :=
    (SpatialRotation.isometry g).injective.comp injective
  cases strict
  · simp only [Bool.false_eq_true, ite_false, finiteHullNormalCone, Set.mem_ofPred_eq, inner_unrotate]
  · simp only [ite_true, strictVoronoiCone,
      mem_interior_finiteHullNormalCone_iff injective a,
      mem_interior_finiteHullNormalCone_iff rotated a, inner_unrotate]

/-- The selected literal upper-roof faces have exactly the desired weak normal label. -/
theorem upperRoof_normalSlope_mem_iff (qbig : 100 ≤ q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    let frame := R.rotatedCertificateNorthFrame hq genuine g
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    ∀ f : normals.UpperFace,
      roof.normalSlope f ∈ convexHull ℝ (Set.range M.physicalVertex) ↔
        N.normal f.val ∈ finiteHullNormalCone (fun b : meshSites q => linear g (b : Space)) a := by
  let frame := R.rotatedCertificateNorthFrame hq genuine g
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  exact fun f => by
    let x := linear g⁻¹ (N.normal f.val)
    have positive : 0 < inner ℝ x (a : Space) := by
      have h : 0 < R.certificateNorthFrame hq genuine x 2 := f.property
      rwa [R.certificateNorthFrame_height hq genuine] at h
    change ((R.certificateNorthFrame hq genuine x 2)⁻¹ •
      Cap.horizontal (R.certificateNorthFrame hq genuine x) ∈ _) ↔ _
    rw [R.certificateNorthFrame_slope_mem_iff hq qbig outward genuine positive]
    exact unrotate_mem_VoronoiCone g false (N.normal f.val)

/-- A strictly labeled original face is in the upper roof and its exact
support slope lies in the interior of the certificate polygon. -/
theorem upperRoof_exists_of_strictVoronoiCone (qbig : 100 ≤ q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (f : Face)
    (chosen : N.normal f ∈ strictVoronoiCone (fun b : meshSites q => linear g (b : Space)) a) :
    let frame := R.rotatedCertificateNorthFrame hq genuine g
    let normals := N.rotate frame
    let roof := (P.rotate frame).upperRoof normals
    ∃ u : normals.UpperFace, u.val = f ∧
      roof.normalSlope u ∈ interior (convexHull ℝ (Set.range M.physicalVertex)) := by
  let frame := R.rotatedCertificateNorthFrame hq genuine g
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let x := linear g⁻¹ (N.normal f)
  have unit : ‖x‖ = 1 := (norm_unrotate g _).trans (N.unit f)
  have original : x ∈ strictVoronoiCone (fun b : meshSites q => (b : Space)) a :=
    (unrotate_mem_VoronoiCone g true (N.normal f)).mpr chosen
  have sphere : x ∈ sphericalVoronoiCell (fun b : meshSites q => (b : Space)) a :=
    ⟨interior_subset original, by simpa only [Metric.mem_sphere, dist_zero_right] using unit⟩
  have positive : 0 < normals.normal f 2 := by
    change 0 < R.certificateNorthFrame hq genuine x 2
    rw [R.certificateNorthFrame_height hq genuine]
    exact inner_pos_of_mem_meshSphericalCell hq a sphere
  refine ⟨⟨f, positive⟩, rfl, ?_⟩
  exact R.certificateNorthFrame_slope_mem_interior hq qbig outward genuine unit original

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
