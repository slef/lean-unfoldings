module

public import Unfoldings.Roof.CompatibleCutMesh
public import Unfoldings.Roof.PotentialCutDisk
public import Unfoldings.Roof.SpatialEnvelopeProjection

/-! Construct increasing fine-edge parents supported on the actual bounded compatible cuts. -/

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

local instance compatibleMeshForestIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

/-- Local common-potential increase chooses actual fine seams. Boundary roots and unused
flat vertices are the only marked roots; the cut disk is derived, not supplied. -/
def compatibleMeshForest : (Q).PotentialCutForest
    ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height
    (R.truncatedCarrier level higher) := by
  apply (Q).potentialCutForest
  intro v nonboundary member
  have interior_point := ((Q).projectedVertex_mem_interior_iff v).mpr nonboundary
  rw [(T).toTriangulation.roof_footprint conforming inside] at interior_point
  have in_sublevel : (Q).projectedVertex v ∈
      interior {x | (K.clippedExtension slopes compact nonempty).height x ≤ level} := by
    rwa [M.clip_eq_sublevel, neg_neg] at interior_point
  have growth := K.truncated_local_growth compact nonempty R no_boundary level higher
    positive beta acute inner_disk member in_sublevel
  have seam_cover : R.truncatedCarrier level higher ∩
      interior {x | (K.clippedExtension slopes compact nonempty).height x ≤ level} ⊆
        ⋃ s : {s : (T).pairedComplex.Seam //
          s ∉ (T).toTriangulation.retainOutside (R.truncatedCarrier level higher)},
            ((Q).projectedTriangle ((T).pairedComplex.left s.val).face).edge
              ((T).pairedComplex.left s.val).edge := by
    intro p hp
    have in_clip : p ∈ interior (SpatialEnvelope.clip M.plane (-level)) := by
      rw [M.clip_eq_sublevel, neg_neg]
      exact hp.2
    obtain ⟨s, cut, on_edge⟩ := K.compatibleCutMesh_cut_seam compact nonempty R no_boundary
      level higher M positive inner_disk hp.1 in_clip
    apply Set.mem_iUnion.mpr
    refine ⟨⟨s, cut⟩, ?_⟩
    rw [(T).toTriangulation.roof_projectedTriangle conforming inside]
    exact on_edge
  obtain ⟨w, s, cut, link, larger⟩ := (Q).exists_potential_ascending_seam
    ((T).toTriangulation.retainOutside (R.truncatedCarrier level higher)) _
    ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).convex_height v
    (growth.mono seam_cover)
  refine ⟨w, s, link, larger, ?_⟩
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside]
  exact not_not.mp cut

theorem compatibleMeshForest_curvature_covered (convex : Convex ℝ slopes)
    (v : (T).pairedComplex.Vertex Set.univ)
    (curved : 0 < (T).pairedComplex.interiorAngularDefect Set.univ v) :
    (Q).projectedVertex v ∈ R.truncatedCarrier level higher := by
  obtain ⟨⟨f, i⟩, equal, _height⟩ := K.clippedPhysical_positive_curvature_original_corner
    compact nonempty M (T).toTriangulation conforming inside convex v curved
  have corner := R.vertex_mem_truncatedCarrier level higher
    (C.vertexOfCorner Set.univ (f, i))
  rw [K.projectedVertex_ofCorner] at corner
  exact equal ▸ corner

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

/-- The actual intrinsic metric realization after cutting the constructed fine seams is a disk. -/
def compatibleMeshCutDisk :
    (T).pairedComplex.Realization (Fcut).retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  (Fcut).cutDisk

theorem compatibleMeshCut_interior_flat (convex : Convex ℝ slopes)
    (w : (T).pairedComplex.Vertex (Fcut).retain)
    (internal : ¬ (T).pairedComplex.IsBoundaryVertex (Fcut).retain w) :
    (T).pairedComplex.totalAngle (Fcut).retain w = 2 * Real.pi :=
  (Fcut).interior_flat (K.compatibleMeshForest_curvature_covered compact nonempty R no_boundary
    level higher M positive inner_disk convex) w internal

/-- A constructed flat cut disk and a rigid development with genuine local interior isometries. -/
theorem exists_compatibleMesh_development (convex : Convex ℝ slopes) :
    ∃ D : FacewiseDevelopment (T).pairedComplex (Fcut).retain,
      ∀ x, ‖((Fcut).cutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val) :=
  (Fcut).exists_isometric_development
    (K.compatibleMeshForest_curvature_covered compact nonempty R no_boundary
      level higher M positive inner_disk convex)

end Unfoldings.ConvexRoof
