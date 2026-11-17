module

public import Unfoldings.Roof.CompatibleComparisonFinitePathAssembly
public import Unfoldings.Complex.DirectedBankChain

/-! Complete actual comparison refinements of original cut-bank chains, with unchanged carriers. -/

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

local instance comparisonChainRefinementIndexFintype : Fintype (T).Index :=
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
local instance comparisonChainRefinementNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonChainRefinementWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Every actual original chain made of cut banks has a complete larger-mesh
refinement, with both literal endpoint copies and exactly its whole original carrier.
Fine-bank separation, successor joins and original labels are derived. -/
theorem exists_compatibleMeshProcessedComparison_chain_refinement
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (cut : ∀ i, ¬ (T).pairedComplex.IsBoundaryEdge Set.univ
      ((T).pairedComplex.germEdge (original.point i).val)) :
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
        MapAt[S] '' (T).pairedComplex.boundaryChainTrace original := by
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
  refine ⟨n, fine, ?_, ?_, ?_⟩
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

open Classical in
/-- Any comparison copy whose whole-cut image comes from the original finite mesh
retains the original height bound. This applies to every point of a refined stem. -/
theorem compatibleMeshProcessedComparison_height_le_of_original_image
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (x : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (original : NewMapAt[S,later,ordered] x ∈ Set.range MapAt[S]) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] x)) ≤ level := by
  obtain ⟨y, at_y⟩ := original
  have folded := (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered x).symm.trans
    ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val) at_y).symm.trans
      (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S y))
  have in_clip := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S] y
  rw [M.clip_eq_sublevel, neg_neg] at in_clip
  exact (congrArg (fun z : Space =>
    (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z)) folded).trans_le in_clip

end Unfoldings.ConvexRoof
