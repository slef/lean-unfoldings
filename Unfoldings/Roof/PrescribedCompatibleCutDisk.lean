module

public import Unfoldings.Roof.CompatibleMeshRetention

/-! Intrinsic flat cut disks for exactly the full prescribed compatible cut network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatiblePrescribedDiskIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite


local notation "retain" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) (R.truncatedCarrier level higher)

include beta acute in
theorem compatiblePrescribedCut_rootedForest :
    ((T).pairedComplex.relativeCutGraph retain Set.univ).IsRootedForest
      ((T).pairedComplex.relativeCutRoots Set.univ) := by
  rw [← K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
    M positive inner_disk beta acute]
  exact (Fcut).rootedForest

/-- An intrinsic disk after cutting exactly the meshed original and exterior compatible segments. -/
def compatiblePrescribedCutDisk :
    (T).pairedComplex.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1 := by
  rw [← K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
    M positive inner_disk beta acute]
  exact (Fcut).cutDisk

include beta acute in
theorem compatiblePrescribedCut_interior_flat (convex : Convex ℝ slopes) :
    ∀ w : (T).pairedComplex.Vertex retain, ¬ (T).pairedComplex.IsBoundaryVertex retain w →
      (T).pairedComplex.totalAngle retain w = 2 * Real.pi := by
  rw [← K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
    M positive inner_disk beta acute]
  exact (Fcut).interior_flat (K.compatibleMeshForest_curvature_covered compact nonempty R
    no_boundary level higher M positive inner_disk convex)

include beta acute in
/-- The prescribed whole cut network gives a genuine flat disk and a locally isometric development.
The development is allowed to overlap until the gap theorem is applied. -/
theorem exists_prescribedCompatibleCut_development (convex : Convex ℝ slopes) :
    ∃ disk : (T).pairedComplex.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
      ∃ D : FacewiseDevelopment (T).pairedComplex retain,
        ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
          Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val) := by
  rw [← K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
    M positive inner_disk beta acute]
  exact ⟨(Fcut).cutDisk, (Fcut).exists_isometric_development
    (K.compatibleMeshForest_curvature_covered compact nonempty R no_boundary level higher
      M positive inner_disk convex)⟩

end Unfoldings.ConvexRoof
