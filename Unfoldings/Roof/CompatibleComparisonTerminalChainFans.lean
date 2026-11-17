module

public import Unfoldings.Roof.CompatibleComparisonTerminalChainModel

/-! Whole original halfplane fans at the actual hinges of constructed terminal-bank chains. -/

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

local instance comparisonTerminalChainFansIndexFintype : Fintype (T).Index :=
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
local notation "HigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "VAt[" L "," h "]" => R.levelWindowModel M L HigherAt[L,h]
local notation "ProperAt[" L "," h "]" => R.levelWindow_proper M L HigherAt[L,h]
local notation "FullAt[" L "," h "]" => R.levelWindow_full M L HigherAt[L,h]
local notation "DomainAt[" L "]" => SpatialEnvelope.levelEquation_domain M.plane (-L)
local notation "Heights" => Set.eqOn_refl (SpatialEnvelope.height M.plane) _
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_cut_disjoint_interior compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S L h
local notation "ConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RemovedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.removed_edge_mem_cut
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RetainedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.retained_openSeamImage_disjoint
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S L h)

open Classical in
local instance comparisonTerminalChainFansNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChainFansWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {r : {v // v ∈ R.parents.roots}} {side : Bool}
  (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered r side)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}

open Classical in
/-- Every internal hinge of the constructed actual chain carries its complete original
halfplane fan, with the original side, support frame and all tagged spatial coordinates.
Neither the hinge location nor a vertex-copy or fan-matching certificate is assumed. -/
theorem CompatibleComparisonTerminalChainModel.internal_halfplane_chart (i : Fin D.length) :
    let vertex := (NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex
      NewRetainAt[S,later,ordered] (D.chain.point i.succ)
    ∃ radius : ℝ, 0 < radius ∧
      ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells r).anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val = (M.plane (W.partition.support
          ((W.terminalSupportCells r).anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + (D.lower i.succ).val)) ∧
        ∃ chart : Metric.eball ((NewAt[S,later,ordered]).pairedComplex.tangentOrigin
              NewRetainAt[S,later,ordered] vertex) (ENNReal.ofReal radius) ≃ᵢ Metric.ball a radius,
          ∀ (b : (NewAt[S,later,ordered]).pairedComplex.TangentTotal
              NewRetainAt[S,later,ordered] vertex)
            (near : edist ((NewAt[S,later,ordered]).pairedComplex.tangentPoint
                NewRetainAt[S,later,ordered] vertex b)
              ((NewAt[S,later,ordered]).pairedComplex.tangentOrigin
                NewRetainAt[S,later,ordered] vertex) < ENNReal.ofReal radius),
            (M.plane (W.partition.support ((W.terminalSupportCells r).anchor side))).place
              (chart ⟨(NewAt[S,later,ordered]).pairedComplex.tangentPoint
                NewRetainAt[S,later,ordered] vertex b, near⟩).val.val =
                (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
                  ((NewAt[S,later,ordered]).pairedComplex.tangentSurfaceTag
                    NewRetainAt[S,later,ordered] vertex b) := by
  let vertex := (NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex
    NewRetainAt[S,later,ordered] (D.chain.point i.succ)
  let t := offsetNonnegativeIccParameter StartAt[r] (D.lower i.succ)
  have after : R.terminalTime level r < t.val := by
    change _ < _ + (D.lower i.succ).val
    linarith [(D.internal i).1]
  have before : t.val < R.terminalTime later r := by
    change _ + (D.lower i.succ).val < _
    linarith [(D.internal i).2]
  have position : (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      vertex = K.compatibleMeshProcessedComparisonTerminalBank compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered r side t before :=
    (D.vertexPoint i.succ).trans
      (K.compatibleMeshProcessedComparisonTerminalClosedBank_eq_bank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered r side (D.lower i.succ)
          (D.internal i).2)
  exact K.exists_compatibleMeshProcessedComparisonTerminal_vertex_halfplane_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered r side t after
    before vertex position

end Unfoldings.ConvexRoof
