module

public import Unfoldings.Roof.CompatibleComparisonTerminalCompletion
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers

/-! Preserve both actual endpoint vertices of each completed comparison terminal bank. -/

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

local instance comparisonTerminalVerticesIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalVerticesNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalVerticesWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Prescribed terminal endpoints preserve every actual cut copy as a fine vertex. -/
theorem exists_compatibleMeshProcessedComparison_terminal_endpoint_vertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots})
    (x : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (position : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered] x) = R.terminalPoint level r ∨
        Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
          NewRetainAt[S,later,ordered] x) = R.terminalPoint later r) :
    ∃ vertex : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[S,later,ordered] vertex = x := by
  have member : (R.terminalPoint level r, R.terminalPoint later r) ∈ PairsAt[S,later] :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  let pair : {p // p ∈ PairsAt[S,later]} :=
    ⟨(R.terminalPoint level r, R.terminalPoint later r), member⟩
  have different := K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level
    higher M positive inner_disk beta acute S ordered pair
  have segment_inside := K.compatibleMeshProcessedWindowPair_segment_subset_clip compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered.le pair
  have cover := (NewAt[S,later,ordered]).prescribed_segment_eq_union_subedges
    (fun p : {p // p ∈ PairsAt[S,later]} => p.val.1) (fun p => p.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ordered) pair
    (segment_inside (left_mem_segment ℝ _ _)) (segment_inside (right_mem_segment ℝ _ _))
  have new_inside := K.compatible_section_interior compact nonempty R later
    HigherAt[later,ordered] M
  rcases position with first | last
  · exact (NewAt[S,later,ordered]).toTriangulation.exists_vertexPoint_of_segment_endpoint
      ConformingAt[S,later,ordered] new_inside different cover NewRetainAt[S,later,ordered] x first
  · apply (NewAt[S,later,ordered]).toTriangulation.exists_vertexPoint_of_segment_endpoint
      ConformingAt[S,later,ordered] new_inside different.symm _ NewRetainAt[S,later,ordered] x last
    convert cover using 1
    · exact segment_symm ℝ _ _
    · apply Set.ext
      intro z
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨e, on_edge⟩
        refine ⟨⟨e.val, ?_⟩, on_edge⟩
        exact fun p hp => (segment_symm ℝ pair.val.2 pair.val.1).subset (e.property hp)
      · rintro ⟨e, on_edge⟩
        refine ⟨⟨e.val, ?_⟩, on_edge⟩
        exact fun p hp => (segment_symm ℝ pair.val.1 pair.val.2).subset (e.property hp)

open Classical in
/-- Each endpoint of the completed actual bank is an original fine vertex copy. -/
theorem exists_compatibleMeshProcessedComparisonTerminalClosedBank_endpoint_vertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Icc (0 : ℝ) DurationAt[later,r])
    (endpoint : u.val = 0 ∨ u.val = DurationAt[later,r]) :
    ∃ vertex : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] vertex =
        FullBankAt[S,later,ordered,r,side] u := by
  have position := (congrArg Cap.horizontal
    (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side u)).trans
    (SpatialEnvelope.horizontal_point _ _)
  apply K.exists_compatibleMeshProcessedComparison_terminal_endpoint_vertex compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered r _
  rcases endpoint with first | last
  · exact Or.inl (position.trans (congrArg (R.exterior.ray (R.terminalIndex r))
      (by rw [first, add_zero])))
  · exact Or.inr (position.trans (congrArg (R.exterior.ray (R.terminalIndex r))
      (by rw [last]; ring)))

end Unfoldings.ConvexRoof
