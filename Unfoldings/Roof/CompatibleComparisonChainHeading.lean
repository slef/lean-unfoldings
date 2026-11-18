module

public import Unfoldings.Roof.CompatibleComparisonFiniteTurnSum
public import Unfoldings.Roof.CompatibleComparisonChainRefinement
public import Unfoldings.Topology.ChainBlockSum
public import Unfoldings.Complex.BoundaryChainHeadingSum

/-! Complete comparison refinements preserve original unreduced real headings. -/

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

local instance comparisonChainHeadingIndexFintype : Fintype (T).Index :=
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
local instance comparisonChainHeadingNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonChainHeadingWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

open Classical in
/-- Every original starting turn is counted once and every inserted turn vanishes. -/
theorem compatibleMeshProcessedComparison_chain_starting_turns
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m n : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (label : Fin (m + 1) → (T).pairedComplex.DirectedCutBank RetainAt[S])
    (named : ∀ i, (label i).start = original.point i)
    (different : (List.ofFn label).Pairwise (fun a b => a.bank ≠ b.bank))
    (fine : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (covered : ∀ p, (∃ j, fine.point j = p) ↔ ∃ i j,
      (K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered
        (label i).seam (label i).side (label i).flag).chain.point j = p)
    (below : ∀ i, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i))) < level) :
    (∑ j : Fin (n + 1), (Real.pi -
      (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          (fine.point j)))) =
      ∑ i : Fin (m + 1), (Real.pi - (T).pairedComplex.totalAngle RetainAt[S]
        ((T).pairedComplex.boundaryEndVertex RetainAt[S] (original.point i))) := by
  let block (i : Fin (m + 1)) :=
    K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W S later ordered
      (label i).seam (label i).side (label i).flag
  let data (i : Fin (m + 1)) :
      ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
        NewRetainAt[S,later,ordered]).ChainBlock :=
    ⟨(block i).length, (block i).chain⟩
  let weight (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd
      NewRetainAt[S,later,ordered]) : ℝ :=
    Real.pi - (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered] p)
  have apart : ∀ i j, i ≠ j → ∀ k l, (data i).2.point k ≠ (data j).2.point l := by
    intro i j distinct k l
    have banks : (label i).bank ≠ (label j).bank := by
      rcases lt_or_gt_of_ne distinct with before | after
      · exact List.pairwise_ofFn.mp different before
      · exact (List.pairwise_ofFn.mp different after).symm
    exact ((block i).separated (block j) banks k l).1
  calc
    _ = ∑ i, ∑ j, weight ((block i).chain.point j) :=
      fine.sum_of_finite_block_cover data apart covered weight
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have at_start : (K.clippedExtension slopes compact nonempty).height
          (Cap.horizontal ((T).pairedFolding.boundaryPosition (label i).start)) < level := by
        rw [named]
        exact below i
      exact ((block i).sum_starting_turns_eq_original at_start).trans
        (congrArg (fun p => Real.pi - (T).pairedComplex.totalAngle RetainAt[S]
          ((T).pairedComplex.boundaryEndVertex RetainAt[S] p)) (named i))

open Classical in
/-- Whole actual block assembly preserves the unreduced real terminal heading. -/
theorem compatibleMeshProcessedComparison_chain_terminal_heading
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m n : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (label : Fin (m + 1) → (T).pairedComplex.DirectedCutBank RetainAt[S])
    (named : ∀ i, (label i).start = original.point i)
    (different : (List.ofFn label).Pairwise (fun a b => a.bank ≠ b.bank))
    (fine : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (covered : ∀ p, (∃ j, fine.point j = p) ↔ ∃ i j,
      (K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered
        (label i).seam (label i).side (label i).flag).chain.point j = p)
    (below : ∀ i, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i))) < level)
    (first : (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        fine.first) = LiftAt[S,later,ordered,original.first] 0) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading fine (Fin.last n) =
      (T).pairedComplex.boundaryChainRollHeading original (Fin.last m) := by
  have all := K.compatibleMeshProcessedComparison_chain_starting_turns compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered original label named
    different fine covered below
  have angle := K.compatibleMeshProcessedComparisonFiniteBank_original_totalAngle compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered original.first 0
    ((T).pairedComplex.boundaryEndVertex RetainAt[S] original.first)
    ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex
      NewRetainAt[S,later,ordered] fine.first)
    ((T).pairedComplex.directedBoundaryPath_zero original.first) first (below 0)
  exact ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading_last_eq_sum_starting_turns
    fine).trans ((congrArg₂ (fun total angle : ℝ => total - (Real.pi - angle)) all angle).trans
      ((T).pairedComplex.boundaryChainRollHeading_last_eq_sum_starting_turns original).symm)

open Classical in
/-- Construct an exact full comparison refinement with its original real terminal heading. -/
theorem exists_compatibleMeshProcessedComparison_chain_refinement_heading
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (cut : ∀ i, ¬ (T).pairedComplex.IsBoundaryEdge Set.univ
      ((T).pairedComplex.germEdge (original.point i).val))
    (below : ∀ i, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i))) < level) :
    ∃ n : ℕ, ∃ fine : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
        NewRetainAt[S,later,ordered]).Chain n,
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          fine.first) = LiftAt[S,later,ordered,original.first] 0 ∧
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
            fine.last)) = LiftAt[S,later,ordered,original.last] 1 ∧
      NewMapAt[S,later,ordered] '' (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace fine =
        MapAt[S] '' (T).pairedComplex.boundaryChainTrace original ∧
      (NewAt[S,later,ordered]).pairedComplex.boundaryChainRollHeading fine (Fin.last n) =
        (T).pairedComplex.boundaryChainRollHeading original (Fin.last m) := by
  obtain ⟨label, named, different, joined⟩ :=
    (T).pairedComplex.exists_directed_cut_bank_chain_labels original cut
  let banks := List.ofFn label
  have nonempty_path : banks ≠ [] := by
    intro empty
    have zero := List.ofFn_eq_nil_iff.mp empty
    omega
  obtain ⟨n, fine, first, last, covered, trace⟩ :=
    K.exists_compatibleMeshProcessedComparison_bank_path_refinement compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered banks nonempty_path
      different joined
  have head : banks.head nonempty_path = label 0 := List.head_ofFn nonempty_path
  have tail : banks.getLast nonempty_path = label (Fin.last m) := by
    simpa only [Nat.add_sub_cancel] using! List.getLast_ofFn (f := label) nonempty_path
  have as_indices (p) : (∃ j, fine.point j = p) ↔ ∃ i j,
      (K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered
        (label i).seam (label i).side (label i).flag).chain.point j = p := by
    rw [covered]
    constructor
    · rintro ⟨bank, present, j, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
      exact ⟨i, j, equal⟩
    · rintro ⟨i, j, equal⟩
      exact ⟨label i, List.mem_ofFn.mpr ⟨i, rfl⟩, j, equal⟩
  have first_original : (NewAt[S,later,ordered]).pairedComplex.vertexPoint
      NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        fine.first) = LiftAt[S,later,ordered,original.first] 0 := by
    rw [head, named] at first
    exact first
  have heading := K.compatibleMeshProcessedComparison_chain_terminal_heading compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered original label named
    different fine as_indices below first_original
  refine ⟨n, fine, ?_, ?_, ?_, heading⟩
  · rw [head, named] at first
    exact first
  · rw [tail, named] at last
    exact last
  · apply Set.Subset.antisymm
    · rintro x ⟨y, on_fine, position⟩
      rw [trace] at on_fine
      obtain ⟨bank, on_fine⟩ := Set.mem_iUnion.mp on_fine
      obtain ⟨present, u, rfl⟩ := Set.mem_iUnion.mp on_fine
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
      have mapped := K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R
        no_boundary level higher M positive inner_disk beta acute W S later ordered
        (label i).start u
      refine ⟨(T).pairedComplex.directedBoundaryPath (label i).start u, ?_,
        mapped.symm.trans position⟩
      rw [named, (T).pairedComplex.boundaryChainTrace_eq_union_paths]
      exact Set.mem_iUnion.mpr ⟨i, u, rfl⟩
    · rintro x ⟨y, on_original, position⟩
      rw [(T).pairedComplex.boundaryChainTrace_eq_union_paths] at on_original
      obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp on_original
      refine ⟨LiftAt[S,later,ordered,(label i).start] u, ?_, ?_⟩
      · rw [trace]
        exact Set.mem_iUnion.mpr ⟨label i, Set.mem_iUnion.mpr
          ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, u, rfl⟩⟩
      · have mapped := K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R
          no_boundary level higher M positive inner_disk beta acute W S later ordered
          (label i).start u
        exact mapped.trans ((congrArg (fun p => MapAt[S]
          ((T).pairedComplex.directedBoundaryPath p u)) (named i)).trans position)

end Unfoldings.ConvexRoof
