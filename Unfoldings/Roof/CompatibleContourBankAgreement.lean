module

public import Unfoldings.Roof.CompatibleContourFiniteGraft

/-! Constructed gap banks attach at exactly the original whole-cut edge speed. -/

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

local instance compatibleContourBankAgreementIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance compatibleContourBankAgreementWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

/-- Each rolled bank edge uses the literal final rootward germ of its original parent edge. -/
theorem compatibleContourSourceBank_germ
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (k : Fin (LengthAt[contour,event] + 1)) :
    let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]
    (chain.point k).val = ((T).pairedComplex.contourParentBank (Fcut).selection contour
      (Fcut).boundary_roots starts ((Fcut).parents.parent^[k.val] VertexAt[contour,event])
      ((Fcut).parents.iterate_lt_distanceToRoot_not_mem VertexAt[contour,event]
        (by rw [SpanAt[contour,event]]; exact k.isLt)) false).val := by
  let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
    SpanAt[contour,event]]
  apply (T).pairedComplex.sourceBank_original_exit (Fcut).selection contour
    (Fcut).boundary_roots starts
    ((T).pairedComplex.selectedRetain_subset_processed (Fcut).selection
      ((T).pairedComplex.contourFrontier (Fcut).selection contour event.val.succ))
    chain VertexAt[contour,event] SpanAt[contour,event]
  · exact K.compatibleMeshFreshSourceBankChain_original compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts event.val event.property.1
      LengthAt[contour,event] SpanAt[contour,event]
  · exact K.compatibleMeshFreshSourceBankChain_terminal_original compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts event.val event.property.1
      LengthAt[contour,event] SpanAt[contour,event]
  · intro j
    obtain ⟨i, _, raw⟩ := K.compatibleMeshFreshSourceBankChain_contour compact nonempty R
      no_boundary
      level higher M positive inner_disk beta acute contour starts event.val event.property.1
      LengthAt[contour,event] SpanAt[contour,event] j
    exact ⟨i, raw⟩

local notation "ParentMark[" v "," h "," side "," t "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W v h side t
local notation "GapMark[" v "," h "," e "," he "," side "," t "]" =>
  K.compatibleContourGapEdgeMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts models v h e he side t

/-- Every edge of the complete source bank has the length of its literal original exit bank. -/
theorem compatibleContourSourceBank_edge_length
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (k : Fin (LengthAt[contour,event] + 1)) :
    ‖(BankAt[contour,starts,event]).chain.edge k‖ =
      (T).pairedComplex.boundaryBankLength
        ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots starts
          ((Fcut).parents.parent^[k.val] VertexAt[contour,event])
          ((Fcut).parents.iterate_lt_distanceToRoot_not_mem VertexAt[contour,event]
            (by rw [SpanAt[contour,event]]; exact k.isLt)) false) := by
  let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
    SpanAt[contour,event]]
  change ‖((T).pairedComplex.boundaryChainRoll chain).edge k‖ = _
  rw [(T).pairedComplex.boundaryChainRoll_edge_length]
  exact congrArg (fun germ : (T).pairedComplex.Germ =>
    dist (((T).pairedComplex.triangle germ.1.1).vertex
      ((T).pairedComplex.germFarCorner germ).2)
      (((T).pairedComplex.triangle germ.1.1).vertex germ.1.2))
    (K.compatibleContourSourceBank_germ compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event k)

/-- Both sides of every constructed gap have exactly the original closed parent-edge metric.
All bank labels, path indices and lengths are derived from the named contour and routing. -/
theorem edist_compatibleContourGapEdgeMark
    (vertex : (T).pairedComplex.Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex)
    (side : Bool) (s t : unitInterval) :
    edist GapMark[vertex,nonroot,event,member,side,s]
      GapMark[vertex,nonroot,event,member,side,t] =
      edist ParentMark[vertex,nonroot,false,s] ParentMark[vertex,nonroot,false,t] := by
  have ancestor := ((T).pairedComplex.mem_contourSavedGapStack (Fcut).selection contour
    vertex event).mp member
  have on_edge := ((T).pairedComplex.mem_contourEdgeGapStack (Fcut).selection contour
    vertex event).mpr ancestor
  let k := (T).pairedComplex.contourGapBankIndex (Fcut).selection contour vertex nonroot
    event on_edge
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts vertex nonroot false
  have original := (T).pairedComplex.contourGapBankIndex_original (Fcut).selection contour
    vertex nonroot event on_edge
  have length := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts event k
  have named := congrArg (fun v :
      {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots} =>
        (T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots
          starts v.val v.property false)
    (show (⟨(Fcut).parents.parent^[k.val] VertexAt[contour,event],
      (Fcut).parents.iterate_lt_distanceToRoot_not_mem VertexAt[contour,event]
        (by rw [SpanAt[contour,event]]; exact k.isLt)⟩ :
        {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots}) =
        ⟨vertex, nonroot⟩ from Subtype.ext original)
  have length_at_vertex := length.trans (congrArg (T).pairedComplex.boundaryBankLength named)
  have coefficient : (‖(BankAt[contour,starts,event]).chain.edge k‖₊ : ℝ≥0∞) =
      ENNReal.ofReal ((T).pairedComplex.boundaryBankLength bank) := by
    simpa only [ofReal_norm, enorm_eq_nnnorm] using congrArg ENNReal.ofReal length_at_vertex
  have whole := K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W bank s t
  have interval := (T).pairedFolding.edist_directedBoundaryPath_eq_length bank s t
  have first : edist ((models event).edgePoint false k s) ((models event).edgePoint false k t) =
      edist ParentMark[vertex,nonroot,false,s] ParentMark[vertex,nonroot,false,t] := by
    calc
      _ = (‖(BankAt[contour,starts,event]).chain.edge k‖₊ : ℝ≥0∞) * edist s t :=
        (models event).edist_edgePoint false k s t
      _ = ENNReal.ofReal ((T).pairedComplex.boundaryBankLength bank) * edist s t :=
        congrArg (fun r => r * edist s t) coefficient
      _ = _ := interval.symm.trans whole.symm
  cases side
  · exact first
  · exact ((models event).edist_edgePoint_sides k s t).symm.trans first

end Unfoldings.ConvexRoof
