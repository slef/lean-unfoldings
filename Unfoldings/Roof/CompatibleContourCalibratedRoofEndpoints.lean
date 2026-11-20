module

public import Unfoldings.Roof.CompatibleContourFiniteRoofEndpoints
public import Unfoldings.Roof.CompatibleMeshDirectedRoofSector

/-! Calibrate the original roof marks at either endpoint of a finite boundary bank. -/

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

local instance calibratedRoofEndpointMeshFintype : Fintype (T).Index :=
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

local instance calibratedRoofEndpointWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute


local notation "Turn" => TriangleComplex.boundaryTurn D Retain


local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts
local notation "BankLength[" e "]" => TriangleComplex.boundaryBankLength D BankAt[e,false]

private theorem roof_endpoint_length (e : Edge) (s t : Bool) :
    (D).boundaryBankLength (Germ e s t) = BankLength[e] := by
  let B := BankAt[e,s]
  have oriented : (D).boundaryBankLength (Germ e s t) = (D).boundaryBankLength B := by
    cases t
    · rfl
    · have tag : ((D).boundaryEndEquiv Retain (Turn B)).1 =
          ((D).boundaryEndEquiv Retain B).1 :=
        ((D).boundaryEnd_bank_eq_iff Retain _ _).mpr (Or.inr rfl)
      have edges : (D).germEdge (Turn B).val = (D).germEdge B.val := congrArg Subtype.val tag
      change (D).boundaryBankLength (Turn B) = (D).boundaryBankLength B
      rw [(D).boundaryBankLength_eq_edge, (D).boundaryBankLength_eq_edge, edges]
  let F := (T).pairedFolding
  have first := F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
    e.val e.property s
  have second := F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
    e.val e.property false
  exact oriented.trans ((F.boundaryBankLength_eq_germDirection_norm B).trans
    ((congrArg norm (first.trans second.symm)).trans
      (F.boundaryBankLength_eq_germDirection_norm BankAt[e,false]).symm))

set_option maxHeartbeats 1000000 in
-- The whole sector chart and the two normalized marks use the same dependent root.
/-- The original roof wedge has a calibrated sector at arbitrary literal finite bank endpoints. -/
theorem compatibleContourSourceOnlyRoofVertex_markedSectorGerm_of_germs
    (p q : Edge) (ps qs pt qt : Bool) (j : Fin (contour.length + 1))
    (first : Germ p ps pt = (D).boundaryMate Retain (contour.cycle.point j))
    (last : Germ q qs qt = contour.cycle.point j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots)
    (small : (D).totalAngle Retain ((D).boundaryEndVertex Retain (contour.cycle.point j)) <
      2 * Real.pi) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    let mark (b : Bool) (t : unitInterval) :=
      if b then Base (.inl q) qs (finiteSlotParameterize qt t)
      else Base (.inl p) ps (finiteSlotParameterize pt t)
    let length (b : Bool) := if b then BankLength[q] else BankLength[p]
    Nonempty (MarkedSectorGerm (Map VertexAt[w]) ((D).totalAngle Retain w) mark length) := by
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map VertexAt[w]
  let edge (b : Bool) := if b then Germ q qs qt else Germ p ps pt
  let mark (b : Bool) (t : unitInterval) :=
    if b then Base (.inl q) qs (finiteSlotParameterize qt t)
    else Base (.inl p) ps (finiteSlotParameterize pt t)
  let length (b : Bool) := if b then BankLength[q] else BankLength[p]
  have at_w : (D).boundaryEndVertex Retain (Germ p ps pt) = w :=
    (((D).boundaryEnd_vertex_eq_iff Retain _ _).mpr (Or.inr first))
  have next : (D).boundaryMate Retain (Germ p ps pt) = Germ q qs qt := by
    exact (congrArg ((D).boundaryMate Retain) first).trans
      (((D).boundaryMate_involutive Retain (contour.cycle.point j)).trans last.symm)
  have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
    level higher M positive inner_disk beta acute w nonroot
  have original := K.compatibleMesh_directedRoofSectorGerm compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W (Germ p ps pt)
    (at_w.symm ▸ below) (at_w.symm ▸ small)
  dsimp only at original
  rw [at_w, next] at original
  have same_mark : (fun b t => Map ((D).directedBoundaryPath (edge b) t)) = mark := by
    funext b t
    cases b
    · exact (K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W p ps pt t).symm
    · exact (K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W q qs qt t).symm
  have same_length : (fun b => (D).boundaryBankLength (edge b)) = length := by
    funext b
    cases b
    · exact roof_endpoint_length K compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts p ps pt
    · exact roof_endpoint_length K compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts q qs qt
  have germ : Nonempty (MarkedSectorGerm x ((D).totalAngle Retain w)
      (fun b t => Map ((D).directedBoundaryPath (edge b) t))
      (fun b => (D).boundaryBankLength (edge b))) := original
  change Nonempty (MarkedSectorGerm x ((D).totalAngle Retain w) mark length)
  rw [← same_length, ← same_mark]
  exact germ

end Unfoldings.ConvexRoof
