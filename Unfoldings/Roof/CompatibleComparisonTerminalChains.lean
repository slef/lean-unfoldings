module

public import Unfoldings.Roof.CompatibleComparisonTerminalPieces
public import Unfoldings.Complex.IntervalBoundaryChain

/-! Construct ordered actual comparison terminal-bank chains with their original endpoint copies. -/

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

local instance comparisonTerminalChainsIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalChainsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChainsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

open Classical in
/-- Construct the complete actual comparison terminal-bank chain. Every whole forward
fine bank occurs once, with literal intrinsic joins and both original endpoint copies.
No ordering, successor, bank-side or fan-matching certificate is supplied. -/
theorem exists_compatibleMeshProcessedComparisonTerminalBank_chain
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    ∃ n : ℕ, ∃ chain :
        ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
          NewRetainAt[S,later,ordered]).Chain n,
      ∃ index : Fin (n + 1) ≃
        K.compatibleMeshProcessedComparisonTerminalBankEnds compact nonempty R no_boundary level
          higher M positive inner_disk beta acute W S later ordered r side,
      (∀ i, chain.point i = (index i).val) ∧
      Set.range FullBankAt[S,later,ordered,r,side] =
        (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace chain ∧
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          chain.first) =
        FullBankAt[S,later,ordered,r,side]
          ⟨0, le_rfl, (sub_pos.mpr ((R.terminalTime_strictMono r) ordered)).le⟩ ∧
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
            chain.last)) =
        FullBankAt[S,later,ordered,r,side]
          ⟨DurationAt[later,r], (sub_pos.mpr ((R.terminalTime_strictMono r) ordered)).le,
            le_rfl⟩ := by
  let ends := K.compatibleMeshProcessedComparisonTerminalBankEnds compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered r side
  let names : ends ↪
      (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered] :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let curve := FullBankAt[S,later,ordered,r,side]
  have choices (p : ends) := p.property
  choose lower upper forward first last matching using choices
  have covered : Set.range curve =
      ⋃ p : ends,
        Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (names p)) :=
    K.compatibleMeshProcessedComparisonTerminalBank_range_eq_union_directedBanks compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side
  exact (NewAt[S,later,ordered]).pairedComplex.exists_boundaryChain_of_interval_pieces
    (sub_pos.mpr ((R.terminalTime_strictMono r) ordered)) names lower upper forward curve
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side).injective
    matching covered

end Unfoldings.ConvexRoof
