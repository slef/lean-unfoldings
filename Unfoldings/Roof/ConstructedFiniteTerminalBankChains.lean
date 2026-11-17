module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankEdges
public import Unfoldings.Complex.IntervalBoundaryChain

/-! Construct entire original terminal-bank chains with both named endpoint vertices. -/

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

local instance finiteTerminalChainsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance finiteTerminalChainsWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- Both original finite terminal banks construct actual ordered boundary chains. Their
entire intrinsic traces, every original forward bank and both named endpoint copies agree.
No boundary-chain, orientation, bank-side or successor certificate is assumed. -/
theorem exists_compatibleMeshTerminalBank_chain :
    ∃ n : ℕ, ∃ chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n,
      ∃ index : Fin (n + 1) ≃
        K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side,
      (∀ i, chain.point i = (index i).val) ∧
      Set.range (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) = (T).pairedComplex.boundaryChainTrace chain ∧
      (T).pairedComplex.boundaryEndVertex (Fcut).retain chain.first =
        K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side ∧
      (T).pairedComplex.boundaryEndVertex (Fcut).retain
        ((T).pairedComplex.boundaryTurn (Fcut).retain chain.last) =
          K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W r side := by
  classical
  let ends := K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side
  let names : ends ↪ (T).pairedComplex.BoundaryEnd (Fcut).retain :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let curve := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side
  have choices (p : ends) := p.property
  choose lower upper forward first last matching using choices
  have covered : Set.range curve =
      ⋃ p : ends, Set.range ((T).pairedComplex.directedBoundaryPath (names p)) :=
    K.compatibleMeshTerminalBank_range_eq_union_directedBanks compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side
  obtain ⟨n, chain, index, named, trace, start, finish⟩ :=
    (T).pairedComplex.exists_boundaryChain_of_interval_pieces (R.terminalTime_pos level higher r)
      names lower upper forward curve
      (K.compatibleMeshTerminalBank_isClosedEmbedding compact nonempty R no_boundary level higher
        M positive inner_disk beta acute W r side).injective matching covered
  refine ⟨n, chain, index, named, trace, ?_, ?_⟩
  · apply (T).pairedComplex.vertexPoint_injective (Fcut).retain
    exact start.trans (K.vertexPoint_compatibleMeshTerminalStartVertex compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side).symm
  · apply (T).pairedComplex.vertexPoint_injective (Fcut).retain
    exact finish.trans (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side).symm

end Unfoldings.ConvexRoof
