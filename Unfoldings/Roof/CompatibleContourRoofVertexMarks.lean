module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraft
public import Unfoldings.Roof.CompatibleContourPhysicalAgreement
public import Unfoldings.Roof.CompatibleContourRoofMarkSeparation
public import Unfoldings.Roof.CompatibleMeshInteriorFiber
public import Unfoldings.Roof.SelectedParentEndpoint

/-! Interior original roof vertices retain exactly their literal incident bank endpoints. -/

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

local instance contourRoofVertexMarksFintype : Fintype (T).Index :=
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

local instance contourRoofVertexWholeFintype : Fintype W.Index := W.finiteIndex

local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
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

/-- A finite parent mark at an original vertex of the whole roof is one of its literal
endpoint copies, with the original parameter and bank side retained. -/
theorem compatibleContourRoofVertex_eq_parentMark_iff
    (w : (D).Vertex (Fcut).retain) (below : Height[VertexAt[w]] < level)
    (e : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (side : Bool) (t : unitInterval) :
    Base (.inl e) side t = Map VertexAt[w] ↔
      (t = 0 ∧ w = (D).boundaryEndVertex Retain BankAt[e,side]) ∨
        (t = 1 ∧ w = (D).boundaryEndVertex Retain ((D).boundaryTurn Retain BankAt[e,side])) := by
  let bank := BankAt[e,side]
  constructor
  · intro equal
    have spatial := K.restore_compatibleContourParentMark_position compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W
      e.val e.property side t
    have restores := K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W VertexAt[w]
    have same := spatial.symm.trans
      ((congrArg (fun x : W.Cut => (W.partition.restoreCut R.carrier x).val) equal).trans restores)
    have position : (T).pairedFolding.toSpace (Fcut).retain VertexAt[w] =
        (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ Forget[w]) := by
      rw [(D).vertexPoint_vertexForgetCuts, (T).pairedFolding.toSpace_forgetCuts]
    have projected := congrArg Cap.horizontal (same.trans position)
    have endpoints := (Roof).selectedParentLineMap_eq_vertex Selection e Forget[w] t
      ((Cap.horizontal.toAffineMap.apply_lineMap _ _ _).symm.trans projected)
    have mark : Map VertexAt[w] = Map ((D).directedBoundaryPath bank t) := equal.symm
    have point := K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W VertexAt[w] below
      ((D).directedBoundaryPath bank t) mark
    rcases endpoints with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl ⟨rfl, (D).vertexPoint_injective Retain
        (point.trans ((D).directedBoundaryPath_zero bank))⟩
    · exact Or.inr ⟨rfl, (D).vertexPoint_injective Retain
        (point.trans ((D).directedBoundaryPath_one bank))⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact congrArg Map ((D).directedBoundaryPath_zero bank)
    · exact congrArg Map ((D).directedBoundaryPath_one bank)

/-- At an original roof vertex below the completion level there is no tail attachment. -/
theorem compatibleContourRoofVertex_ne_tailMark
    (w : (D).Vertex (Fcut).retain) (below : Height[VertexAt[w]] < level)
    (e : (D).ContourTerminalEdge Selection) (side : Bool) (t : ℝ≥0) :
    Base (.inr e) side t ≠ Map VertexAt[w] := by
  intro equal
  have upper := K.compatibleContourTerminalMark_height_ge compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W e side t
  let height (x : W.Cut) := (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut R.carrier x).val)
  have same := congrArg height equal
  have restores := congrArg
    (fun p : Space => (K.clippedExtension slopes compact nonempty).height (Cap.horizontal p))
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W VertexAt[w])
  exact (not_lt_of_ge (upper.trans_eq (same.trans restores))) below

end Unfoldings.ConvexRoof
