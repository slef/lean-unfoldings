module

public import Unfoldings.Roof.CompatibleComparisonCutBoundary
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.SpatialEnvelopeDirectedBanks
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! Canonical comparison segments preserve endpoint vertices and whole fine-edge alignment. -/

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

local instance comparisonPrescribedGeometryIndexFintype : Fintype (T).Index :=
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
local instance comparisonPrescribedGeometryNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

open Classical in
/-- Every intrinsic copy over either endpoint of a canonical comparison segment is
an actual fine vertex, including copies with different face tags. -/
theorem exists_compatibleMeshProcessedComparison_pair_endpoint_vertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (pair : {p // p ∈ PairsAt[S,later]})
    (x : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (position : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered] x) = pair.val.1 ∨
        Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
          NewRetainAt[S,later,ordered] x) = pair.val.2) :
    ∃ vertex : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[S,later,ordered] vertex = x := by
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
/-- A nonvertex contact with a canonical segment forces the entire fine edge
into that segment, including its two endpoints. -/
theorem compatibleMeshProcessedComparison_pair_segment_aligned
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (pair : {p // p ∈ PairsAt[S,later]})
    (f : (NewAt[S,later,ordered]).Index) (e : Fin 3)
    (x : ((NewAt[S,later,ordered]).projectedTriangle f).Edge e)
    (regular : ¬ ((NewAt[S,later,ordered]).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ segment ℝ pair.val.1 pair.val.2) :
    ((NewAt[S,later,ordered]).projectedTriangle f).edge e ⊆
      segment ℝ pair.val.1 pair.val.2 := by
  let U := triangleWithEdge pair.val.1 pair.val.2
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S ordered pair)
  exact U.edge_subset_of_signed_coords ((NewAt[S,later,ordered]).projectedTriangle f)
    (fun k => (NewAt[S,later,ordered]).signs f (pair, k))
    (fun k p hp => (NewAt[S,later,ordered]).constrained f p hp (pair, k)) 0 e x regular member

open Classical in
/-- A nonvertex contact orients the entire actual fine bank in the canonical
segment's original parameter order, retaining the intrinsic contact copy. -/
theorem exists_compatibleMeshProcessedComparison_forward_pair_bank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (pair : {p // p ∈ PairsAt[S,later]})
    (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
    (u : unitInterval)
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v)
    (member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ pair.val.1 pair.val.2) :
    ∃ (q : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (s t : unitInterval), s.val < t.val ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition q) =
        AffineMap.lineMap pair.val.1 pair.val.2 s.val ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] q)) =
          AffineMap.lineMap pair.val.1 pair.val.2 t.val ∧
      ∃ v : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath q v =
        (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u := by
  let bank := ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
    NewRetainAt[S,later,ordered] p).1
  have aligned := K.compatibleMeshProcessedComparison_pair_segment_aligned compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered pair bank.val.face
    bank.val.edge
    ⟨_, (NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p u⟩
    ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_nonvertex p u regular)
    member
  have entire (v : unitInterval) := aligned
    ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p v)
  have first_member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) ∈
      segment ℝ pair.val.1 pair.val.2 := by
    have initial := entire 0
    rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at initial
    change AffineMap.lineMap _ _ (0 : ℝ) ∈ _ at initial
    simpa only [AffineMap.lineMap_apply_zero] using initial
  have last_member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) ∈
      segment ℝ pair.val.1 pair.val.2 := by
    have final := entire 1
    rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at final
    change AffineMap.lineMap _ _ (1 : ℝ) ∈ _ at final
    simpa only [AffineMap.lineMap_apply_one] using final
  rw [segment_eq_image_lineMap] at first_member last_member
  obtain ⟨s, hs, first⟩ := first_member
  obtain ⟨t, ht, last⟩ := last_member
  have different : s ≠ t := by
    intro same
    exact (NewAt[S,later,ordered]).toTriangulation.horizontal_boundaryPosition_ne p
      (first.symm.trans ((congrArg (AffineMap.lineMap pair.val.1 pair.val.2) same).trans last))
  rcases lt_or_gt_of_ne different with forward | backward
  · exact ⟨p, ⟨s, hs⟩, ⟨t, ht⟩, forward, first.symm, last.symm, u, rfl⟩
  · refine ⟨(NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p,
      ⟨t, ht⟩, ⟨s, hs⟩, backward, last.symm, ?_, ?_⟩
    · rw [(NewAt[S,later,ordered]).pairedComplex.boundaryTurn_involutive]
      exact first.symm
    · refine ⟨⟨1 - u.val, sub_nonneg.mpr u.property.2, sub_le_self _ u.property.1⟩, ?_⟩
      rw [(NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_turn]
      apply congrArg ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p)
      apply Subtype.ext
      change 1 - (1 - u.val) = u.val
      ring

end Unfoldings.ConvexRoof
