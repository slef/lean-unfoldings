module

public import Unfoldings.Roof.CompatibleContourRoofVertexMarks
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Cap.ContourLeafFans

/-! The revised graft's positive leaf keeps one roof vertex and its complementary gap. -/

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
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourSourceOnlyLeafFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)

local instance contourSourceOnlyLeafWholeFintype : Fintype W.Index := W.finiteIndex

local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Forget[" w "]" => TriangleComplex.vertexForgetCuts D (Set.subset_univ Retain) w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))
local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) side

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour

/-- At a positive childless source both literal roof banks reach the same original cut copy.
Its total retained cone angle and the source gap's exact defect add to a full turn. -/
theorem compatibleContourSourceOnlyLeaf_roof_fan (event : Event)
    (nonroot : SourceOf[event] ∉ (Fcut).parents.roots)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    let v := SourceOf[event]
    let edge := (⟨v, nonroot⟩ : {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
    Stack (.inl edge) = [event] ∧ ∃ w : (D).Vertex Retain,
      Forget[w] = v ∧ Height[VertexAt[w]] < level ∧
      ((D).totalAngle Retain w + (D).interiorAngularDefect Set.univ v = 2 * Real.pi) ∧
      ∀ side : Bool, Base (.inl edge) side 0 = Map VertexAt[w] := by
  let cap := (T).toTriangulation.normalizedCap conforming inside
  let v := SourceOf[event]
  let edge := (⟨v, nonroot⟩ : {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
  have internal : ¬ (D).IsBoundaryVertex Set.univ v :=
    fun h => nonroot ((Fcut).boundary_roots h)
  obtain ⟨w, original, angle, unique⟩ :=
    cap.exists_selected_leaf_copy Selection v nonroot internal childless
  have same : (T).pairedFolding.toSpace Retain VertexAt[w] =
      (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ v) := by
    rw [← original, (D).vertexPoint_vertexForgetCuts, (T).pairedFolding.toSpace_forgetCuts]
    rfl
  have below : Height[VertexAt[w]] < level :=
    (congrArg (fun p : Space => (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal p)) same).trans_lt
      (K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M positive
        inner_disk beta acute v nonroot)
  have balance : (D).totalAngle Retain w + (D).interiorAngularDefect Set.univ v =
      2 * Real.pi := by
    calc
      _ = (D).totalAngle Set.univ v + (D).interiorAngularDefect Set.univ v :=
        congrArg (fun θ => θ + (D).interiorAngularDefect Set.univ v) angle
      _ = _ := by
        rw [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
        ring
  refine ⟨(D).contourSavedGapStack_leaf Selection contour (Fcut).boundary_roots starts
    event nonroot childless, w, original, below, balance, ?_⟩
  intro side
  have bank := (D).contourParentBank_start Selection contour (Fcut).boundary_roots starts
    v nonroot side
  have at_copy : (D).boundaryEndVertex Retain BankAt[edge,side] = w :=
    unique _ bank
  exact (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W w below edge side 0).mpr
    (Or.inl ⟨rfl, at_copy.symm⟩)

end Unfoldings.ConvexRoof
