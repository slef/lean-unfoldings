module

public import Unfoldings.Roof.CompatibleComparisonFinitePathAssembly
public import Unfoldings.Complex.DirectedBankChain
public import Unfoldings.Geometry.RadialMarginSubdivision
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Geometry.RadialChain

/-! Actual comparison refinements preserve every quantitative projected radial margin. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

private theorem comparison_path_union_image {A X Y Z : Type*} {n : ℕ}
    (label : Fin n → A) (f : X → Z) (g : Y → Z)
    (p : A → unitInterval → X) (q : Fin n → unitInterval → Y)
    (pointwise : ∀ i u, f (p (label i) u) = g (q i u)) :
    f '' (⋃ a ∈ List.ofFn label, Set.range (p a)) = g '' (⋃ i, Set.range (q i)) := by
  ext z
  constructor
  · rintro ⟨x, member, at_z⟩
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨present, u, rfl⟩ := Set.mem_iUnion.mp member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
    exact ⟨q i u, Set.mem_iUnion.mpr ⟨i, u, rfl⟩, (pointwise i u).symm.trans at_z⟩
  · rintro ⟨y, member, at_z⟩
    obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨p (label i) u, Set.mem_iUnion.mpr ⟨label i,
      Set.mem_iUnion.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, u, rfl⟩⟩,
      (pointwise i u).trans at_z⟩

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

local instance comparisonChainMarginIndexFintype : Fintype (T).Index :=
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
local instance comparisonChainMarginNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonChainMarginWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Every fine comparison bank keeps the original dimensionless radial margin.
The actual chain, its complete old-bank coverage and all forward parameters are
constructed; no new edge-direction or radial certificate is supplied. -/
theorem exists_compatibleMeshProcessedComparison_chain_radial_margin
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (cut : ∀ i, ¬ (T).pairedComplex.IsBoundaryEdge Set.univ
      ((T).pairedComplex.germEdge (original.point i).val))
    (source : Plane) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : ∀ i,
      γ * (‖Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i)) - source‖ *
        ‖Cap.horizontal ((T).pairedFolding.germDirection (original.point i).val)‖) ≤
      inner ℝ (Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i)) - source)
        (Cap.horizontal ((T).pairedFolding.germDirection (original.point i).val))) :
    ∃ n : ℕ, ∃ fine : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
        NewRetainAt[S,later,ordered]).Chain n,
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          fine.first) = LiftAt[S,later,ordered,original.first] 0 ∧
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
            fine.last)) = LiftAt[S,later,ordered,original.last] 1 ∧
      Set.range ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain fine).path =
        Set.range ((T).pairedFolding.projectedBoundaryChain original).path ∧
      (∀ j,
        γ * (‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
            (fine.point j)) - source‖ *
          ‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
            (fine.point j).val)‖) ≤
        inner ℝ (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
          (fine.point j)) - source)
          (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
            (fine.point j).val))) ∧
      ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain fine).RadialFrom source 0 := by
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
  have fine_margin (j : Fin (n + 1)) :
      γ * (‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
          (fine.point j)) - source‖ *
        ‖Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
          (fine.point j).val)‖) ≤
      inner ℝ (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        (fine.point j)) - source)
        (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.germDirection
          (fine.point j).val)) := by
    obtain ⟨bank, present, k, same⟩ := (covered (fine.point j)).mp ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
    let D := K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered
      (label i).seam (label i).side (label i).flag
    change D.chain.point k = fine.point j at same
    rw [← same, D.first, D.spatialVector,
      (T).pairedFolding.directedBoundaryPath_position, map_add, map_smul, map_smul]
    have starting : (OldEndAt[S,(label i).seam,(label i).side,(label i).flag]) =
        original.point i := named i
    rw [starting]
    have bound := radial_margin_forward_piece nonnegative small (D.lower k).property.1
      (sub_nonneg.mpr (D.forward k).le) (margin i)
    convert bound using 1 <;> abel_nf
  have head : banks.head nonempty_path = label 0 := List.head_ofFn nonempty_path
  have tail : banks.getLast nonempty_path = label (Fin.last m) := by
    simpa only [Nat.add_sub_cancel] using! List.getLast_ofFn (f := label) nonempty_path
  rw [head, named] at first
  rw [tail, named] at last
  have carrier :
      Set.range ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain fine).path =
        Set.range ((T).pairedFolding.projectedBoundaryChain original).path := by
    rw [SpatialFolding.projectedBoundaryChain_path_range,
      SpatialFolding.projectedBoundaryChain_path_range, trace,
      (T).pairedComplex.boundaryChainTrace_eq_union_paths]
    refine comparison_path_union_image label
      (Cap.horizontal ∘ (NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered])
      (Cap.horizontal ∘ (T).pairedFolding.toSpace RetainAt[S])
      (fun bank => (LiftAt[S,later,ordered,bank.start] : unitInterval → _))
      (fun i => (T).pairedComplex.directedBoundaryPath (original.point i)) ?_
    intro i u
    have folded := K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      (label i).start u
    exact (congrArg Cap.horizontal folded).trans
      (congrArg (fun p => Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath p u))) (named i))
  refine ⟨n, fine, first, last, carrier, fine_margin, ?_⟩
  intro j _
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  have bound := fine_margin j
  rw [← (NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc fine j,
    ← (NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_edge fine j] at bound
  exact (mul_nonneg nonnegative (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans bound

end Unfoldings.ConvexRoof
