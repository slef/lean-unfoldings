module

public import Unfoldings.Complex.ContourSourceCoverage
public import Unfoldings.Roof.ConstructedFiniteTerminalBoundary
public import Unfoldings.Roof.Topology
public import Unfoldings.Roof.PotentialContourHistory

/-! The actual compatible roof contour can spend each positive defect before its wrap. -/

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
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)


variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside

local instance completeMeshContourIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

/-- Choose an actual original rim anchor for which every positive fine-roof defect
has a source event in the source-only construction. -/
theorem exists_compatibleMesh_completeSourceContour (convex : Convex ℝ slopes) :
    ∃ contour : (T).pairedComplex.BoundaryContour (Fcut).retain,
      (T).pairedComplex.contourOriginalVertex (Fcut).selection contour 0 ∈ (Fcut).parents.roots ∧
      (T).pairedComplex.contourOriginalVertex (Fcut).selection contour (Fin.last contour.length) ∈
        (Fcut).parents.roots ∧
      ∀ v : (T).pairedComplex.Vertex Set.univ,
        0 < (T).pairedComplex.interiorAngularDefect Set.univ v →
        ∃ e : (T).pairedComplex.PositiveContourSource (Fcut).selection contour,
          (T).pairedComplex.positiveContourVertex (Fcut).selection contour e = v := by
  let D := (T).pairedComplex
  let S := (Fcut).selection
  let original := K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher
    M positive inner_disk beta acute
  obtain ⟨contour, starts, ends⟩ := D.exists_contour_starts_ends_root_of_disk S original
    (T).pairedFolding (Q).diskHomeomorph (Fcut).boundary_roots
  refine ⟨contour, starts, ends, ?_⟩
  intro v positive_defect
  have nonroot : v ∉ (Fcut).parents.roots := by
    intro root
    rw [(Fcut).roots_eq] at root
    rcases root with bound | outside
    · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left bound] at positive_defect
      exact (lt_irrefl _ positive_defect)
    · exact outside (K.compatibleMeshForest_curvature_covered compact nonempty R no_boundary
        level higher M positive inner_disk convex v positive_defect)
  exact D.exists_positiveContourSource_of_defect S contour (Fcut).boundary_roots
    starts ends v nonroot positive_defect

end Unfoldings.ConvexRoof
