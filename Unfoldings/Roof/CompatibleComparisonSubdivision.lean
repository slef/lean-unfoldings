module

public import Unfoldings.Roof.CompatibleProcessedComparisonMesh
public import Unfoldings.Geometry.NestedSpatialSubdivision
public import Unfoldings.Roof.NestedSubdivisionAngles

/-! Larger comparison meshes preserve old faces as actual isometric subdivisions. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

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

local instance comparisonSubdivisionOldFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h

open Classical in
local instance comparisonSubdivisionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

open Classical in
/-- Every old closed physical face is covered by whole contained comparison triangles. -/
theorem compatibleMeshProcessedComparisonMesh_faceRefinement
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :
    (T).toTriangulation.FaceRefinement (NewAt[S,later,ordered]).toTriangulation := by
  apply (T).toTriangulation.faceRefinement_of_constraints
    (K.compatibleMeshProcessedComparisonRefinementMesh compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered) ?_ Sum.inr ?_
  · intro p member
    rw [M.clip_eq_sublevel, neg_neg] at member ⊢
    exact member.trans ordered.le
  · intro j
    change ((Q).projectedTriangle j.1).coord j.2 = _
    rw [(T).toTriangulation.roof_projectedTriangle conforming inside]

open Classical in
/-- The larger mesh restricted to old faces is an actual Euclidean subdivision. -/
def compatibleMeshProcessedComparisonSubdivision
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :=
  (T).toTriangulation.nestedSubdivision (NewAt[S,later,ordered]).toTriangulation
    (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered)

open Classical in
/-- The actual larger comparison mesh conserves every original physical corner angle. -/
theorem compatibleMeshProcessedComparisonSubdivision_cornerAnglePreserving
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :
    (K.compatibleMeshProcessedComparisonSubdivision compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S later ordered).CornerAnglePreserving :=
  (T).toTriangulation.nestedSubdivision_cornerAnglePreserving
    (NewAt[S,later,ordered]).toTriangulation
    (K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered)
    (K.compatible_section_interior compact nonempty R later (fun v => (higher v).trans ordered) M)
    (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered)

end Unfoldings.ConvexRoof
