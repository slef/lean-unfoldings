module

public import Unfoldings.Roof.CompatibleComparisonFiniteBlockJoins
public import Unfoldings.Complex.DirectedCutBank
public import Unfoldings.Topology.ChainBlockAssembly

/-! Assemble the complete actual comparison refinement of a finite original cut-bank path. -/

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

local instance comparisonFinitePathAssemblyIndexFintype : Fintype (T).Index :=
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
local instance comparisonFinitePathAssemblyNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFinitePathAssemblyWholeFintype : Fintype W.Index := W.finiteIndex

local notation "OldEndAt[" S "," s "," side "," flag "]" =>
  Equiv.symm (TriangleComplex.boundaryEndEquiv
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) RetainAt[S])
    (TriangleComplex.cutBank (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) RetainAt[S] s side, flag)
local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

open Classical in
/-- A nonrepeating original directed bank path constructs one complete actual
comparison chain. Original retained corner joins derive all fine successors. -/
theorem exists_compatibleMeshProcessedComparison_bank_path_refinement
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (banks : List ((T).pairedComplex.DirectedCutBank RetainAt[S])) (nonempty_path : banks ≠ [])
    (different : banks.Pairwise (fun a b => a.bank ≠ b.bank))
    (joined : banks.IsChain (fun a b =>
      (T).pairedComplex.vertexOfCorner RetainAt[S] a.finishCorner =
        (T).pairedComplex.vertexOfCorner RetainAt[S] b.startCorner)) :
    ∃ n : ℕ, ∃ chain : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
        NewRetainAt[S,later,ordered]).Chain n,
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          chain.first) = LiftAt[S,later,ordered,(banks.head nonempty_path).start] 0 ∧
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
            chain.last)) = LiftAt[S,later,ordered,(banks.getLast nonempty_path).start] 1 ∧
      (∀ p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered],
        (∃ i, chain.point i = p) ↔ ∃ bank ∈ banks, ∃ i,
          (K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary level
            higher M positive inner_disk beta acute W S later ordered
            bank.seam bank.side bank.flag).chain.point i = p) ∧
      (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace chain =
        ⋃ bank ∈ banks, Set.range LiftAt[S,later,ordered,bank.start] := by
  let D := (NewAt[S,later,ordered]).pairedComplex
  let kept := NewRetainAt[S,later,ordered]
  let P := D.boundarySystem kept
  let block (bank : (T).pairedComplex.DirectedCutBank RetainAt[S]) :=
    K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered bank.seam bank.side bank.flag
  let blockData (bank : (T).pairedComplex.DirectedCutBank RetainAt[S]) : P.ChainBlock :=
    ⟨(block bank).length, (block bank).chain⟩
  let pieces : List P.ChainBlock := banks.map blockData
  have pieces_nonempty : pieces ≠ [] := by
    intro empty
    exact nonempty_path (List.map_eq_nil_iff.mp empty)
  have apart : pieces.Pairwise P.ChainBlocksSeparated := by
    apply List.pairwise_map.mpr
    exact different.imp (fun {_ _} distinct => (block _).separated (block _) distinct)
  have fine_joined : pieces.IsChain P.ChainBlocksJoined := by
    apply (List.isChain_map _).mpr
    apply List.isChain_iff_getElem.mpr
    intro i bound
    apply (block banks[i]).joined (block banks[i + 1])
      (List.isChain_iff_getElem.mp different.isChain i bound)
    change (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] banks[i].start) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] banks[i + 1].start
    rw [TriangleComplex.DirectedCutBank.finish_vertex, TriangleComplex.DirectedCutBank.start_vertex]
    exact List.isChain_iff_getElem.mp joined i bound
  obtain ⟨n, chain, first, last, covered⟩ := P.exists_chain_of_blocks pieces pieces_nonempty
    apart fine_joined
  have first_eq : chain.first = (block (banks.head nonempty_path)).chain.first :=
    first.trans (congrArg (fun piece : P.ChainBlock => piece.2.first)
      (List.head_map (f := blockData) pieces_nonempty))
  have last_eq : chain.last = (block (banks.getLast nonempty_path)).chain.last :=
    last.trans (congrArg (fun piece : P.ChainBlock => piece.2.last)
      (List.getLast_map (f := blockData) pieces_nonempty))
  have named (p : D.BoundaryEnd kept) : (∃ i, chain.point i = p) ↔
      ∃ bank ∈ banks, ∃ i, (block bank).chain.point i = p := by
    rw [covered]
    constructor
    · rintro ⟨piece, member, i, equal⟩
      obtain ⟨bank, present, rfl⟩ := List.mem_map.mp member
      exact ⟨bank, present, i, equal⟩
    · rintro ⟨bank, present, i, equal⟩
      exact ⟨⟨(block bank).length, (block bank).chain⟩,
        List.mem_map.mpr ⟨bank, present, rfl⟩, i, equal⟩
  have trace : D.boundaryChainTrace chain =
      ⋃ bank ∈ banks, Set.range LiftAt[S,later,ordered,bank.start] := by
    apply Set.Subset.antisymm
    · intro x member
      rw [D.boundaryChainTrace_eq_union_paths] at member
      obtain ⟨i, u, position⟩ := Set.mem_iUnion.mp member
      obtain ⟨bank, present, j, equal⟩ := (named (chain.point i)).mp ⟨i, rfl⟩
      have in_block : x ∈ D.boundaryChainTrace (block bank).chain := by
        rw [D.boundaryChainTrace_eq_union_paths]
        exact Set.mem_iUnion.mpr ⟨j, u,
          (congrArg (fun p => D.directedBoundaryPath p u) equal).trans position⟩
      exact Set.mem_iUnion.mpr ⟨bank, Set.mem_iUnion.mpr
        ⟨present, (block bank).trace.symm.subset in_block⟩⟩
    · intro x member
      obtain ⟨bank, member⟩ := Set.mem_iUnion.mp member
      obtain ⟨present, on_bank⟩ := Set.mem_iUnion.mp member
      have in_block := (block bank).trace.subset on_bank
      rw [D.boundaryChainTrace_eq_union_paths] at in_block
      obtain ⟨j, u, position⟩ := Set.mem_iUnion.mp in_block
      obtain ⟨i, equal⟩ := (named ((block bank).chain.point j)).mpr ⟨bank, present, j, rfl⟩
      rw [D.boundaryChainTrace_eq_union_paths]
      exact Set.mem_iUnion.mpr ⟨i, u,
        (congrArg (fun p => D.directedBoundaryPath p u) equal).trans position⟩
  refine ⟨n, chain, ?_, ?_, named, trace⟩
  · rw [first_eq]
    exact (block (banks.head nonempty_path)).first_point
  · rw [last_eq]
    exact (block (banks.getLast nonempty_path)).last_point

end Unfoldings.ConvexRoof
