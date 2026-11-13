module

public import Unfoldings.Roof.CompletionExtendedMesh
public import Unfoldings.Roof.ExtendedCutGrowth
public import Unfoldings.Roof.CompletionRadialCurvature
public import Unfoldings.Cap.OutwardRadialForest

/-! Construct an actual outward auxiliary forest from the original forest and radial tails. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

/-- Every selected fine edge points outward along its whole length. Unused flat vertices may
remain isolated roots; every component containing an actual cut edge ends on the outer rim. -/
def completionOutwardForest (positive : 0 < t) (small : t < 1) :
    let F := E.cornerTails M.inside
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    {R : L.cap.RadialCutForest origin (M.extendedGeometricCuts F) // R.Outward} := by
  let F := E.cornerTails M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let Q := L.cap
  change {R : Q.RadialCutForest origin (M.extendedGeometricCuts F) // R.Outward}
  apply Q.outwardRadialCutForest
  intro v nonboundary member
  have in_clip : Q.projectedVertex v ∈ interior
      (SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level) := by
    have interior_point := (Q.projectedVertex_mem_interior_iff v).mpr nonboundary
    rw [L.cap_footprint] at interior_point
    exact interior_point
  have growth := M.extended_local_growth positive small F
    (E.cornerTails_covers_rim M.inside) member in_clip
  have seam_cover : M.extendedGeometricCuts F ∩ interior
      (SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level) ⊆
      ⋃ s : {s : L.mesh.toTriangulation.pairedComplex.Seam // s ∉ M.extendedRetain E},
        (Q.projectedTriangle (L.mesh.toTriangulation.pairedComplex.left s.val).face).edge
          (L.mesh.toTriangulation.pairedComplex.left s.val).edge := by
    intro p hp
    obtain ⟨s, cut, on_edge⟩ := M.extended_cut_seam E hp.1 hp.2
    refine Set.mem_iUnion.mpr ⟨⟨s, cut⟩, ?_⟩
    exact (L.mesh.toTriangulation.normalizedCap_projectedTriangle_edge
      L.conforming L.interior_nonempty _ _).symm.subset on_edge
  obtain ⟨w, s, cut, link, farther, outward⟩ := Q.exists_outward_cut_seam
    (M.extendedRetain E) origin v (growth.mono seam_cover)
  refine ⟨w, s, link, farther, ?_, outward⟩
  have selected : (L.mesh.projectedTriangle (L.mesh.toTriangulation.pairedComplex.left s).face).edge
      (L.mesh.toTriangulation.pairedComplex.left s).edge ⊆ M.extendedGeometricCuts F :=
    not_not.mp cut
  exact (L.mesh.toTriangulation.normalizedCap_projectedTriangle_edge
    L.conforming L.interior_nonempty _ _).subset.trans selected

/-- The constructed auxiliary cut disk has an actual locally isometric development. -/
theorem completionOutward_exists_development (positive : 0 < t) (small : t < 1)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    let R := (M.completionOutwardForest E positive small).val
    ∃ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
      ∀ x, ‖(R.cutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val) := by
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest E positive small).val
  exact R.exists_development (M.radialMesh_curvature_covered E height)

end Unfoldings.ConvexRoof.SectorForest
