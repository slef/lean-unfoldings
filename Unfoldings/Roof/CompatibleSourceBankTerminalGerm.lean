module

public import Unfoldings.Roof.CompatibleSourceBankTerminal
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.ProcessedParentSegments
public import Unfoldings.Roof.TerminalJunctionGerm

/-! Complete source banks retain the exact original cut germ at their terminal junctions. -/

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

local instance sourceBankTerminalGermIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h
local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S

/-- The full incoming original last bank is cut, even for a source directly adjacent to the rim. -/
theorem compatibleSourceBank_last_segment_cut
    (S : (Fcut).parents.ParentFrontier) {m : ℕ}
    (chain : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (source : (T).pairedComplex.Vertex Set.univ) (processed : source ∈ S.processed)
    (span : (Fcut).parents.distanceToRoot source = m + 1)
    (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] source)
    (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root source) :
    segment ℝ (((T).pairedFolding.projectedBoundaryChain chain).vertex (Fin.last m).castSucc)
      (((T).pairedFolding.projectedBoundaryChain chain).vertex (Fin.last (m + 1))) ⊆ CutsAt[S] := by
  have geometry := K.compatibleSourceBankChain_eq_history compact nonempty R no_boundary level
    higher M positive inner_disk beta acute chain source span labels terminal
  rw [geometry]
  change segment ℝ ((Q).projectedVertex ((Fcut).parents.parent^[m] source))
    ((Q).projectedVertex ((Fcut).parents.parent^[m + 1] source)) ⊆ CutsAt[S]
  rw [Function.iterate_succ_apply']
  have selected := (Fcut).processed_parent_segment_subset S ((Fcut).parents.parent^[m] source)
    ((Fcut).parents.iterate_lt_distanceToRoot_not_mem source (by rw [span]; omega))
    (S.iterate_mem_of_mem processed m)
  exact fun p member => Or.inr (selected member)

/-- At the true terminal junction the current processed cut and the complete original cut
have identical local carriers. All incoming-bank and outer-ray data are constructed. -/
theorem exists_compatibleSourceBank_terminal_cut_germ
    (S : (Fcut).parents.ParentFrontier) {m : ℕ}
    (chain : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (source : (T).pairedComplex.Vertex Set.univ) (processed : source ∈ S.processed)
    (span : (Fcut).parents.distanceToRoot source = m + 1)
    (labels : ∀ k : Fin (m + 1), (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] source)
    (terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z,
      dist z (R.terminalPoint level RootAt[source,by omega]) < ε →
        (z ∈ R.carrier ↔ z ∈ CutsAt[S]) := by
  have geometry := K.compatibleSourceBankChain_eq_history compact nonempty R no_boundary level
    higher M positive inner_disk beta acute chain source span labels terminal
  obtain ⟨s, nonnegative, before, first⟩ := K.exists_compatibleMeshHistory_terminal_arrival compact
    nonempty R no_boundary level higher M positive inner_disk beta acute source m span
  have last := K.compatibleMeshHistory_last_terminalPoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute source (m + 1) (by omega) span
  rw [← geometry] at first last
  have selected := K.compatibleSourceBank_last_segment_cut compact nonempty R no_boundary level
    higher M positive inner_disk beta acute S chain source processed span labels terminal
  rw [first, last] at selected
  exact K.exists_terminal_junction_cut_germ compact nonempty R no_boundary level higher
    CutsAt[S] IncludedAt[S] (fun _ member => Or.inl member) RootAt[source,by omega]
    nonnegative before selected

end Unfoldings.ConvexRoof
