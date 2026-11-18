module

public import Unfoldings.Roof.CompatibleProcessedWindowSegments
public import Unfoldings.Roof.CompatiblePartialWindowLift
public import Unfoldings.Roof.CompatibleLevelWindow
public import Unfoldings.Roof.CompletionOriginalPieces
public import Unfoldings.Geometry.ConstrainedTriangulationSelection

/-! Construct actual larger meshes of the same intermediate original whole cut. -/

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

local instance processedComparisonMeshIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

open Classical in
/-- Original segment supports and endpoint lines for the same cut in a larger window. -/
def compatibleMeshProcessedComparisonEquations (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    ({p // p ∈ PairsAt[S,later]} × Fin 3) → Plane →ᵃ[ℝ] ℝ :=
  segmentEquations (fun p => p.val.1) (fun p => p.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ordered)

local notation "EquationsAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonEquations compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h

open Classical in
/-- All newly constructed comparison constraints are proper original geometric lines. -/
theorem compatibleMeshProcessedComparisonEquations_ne_zero (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (j) : EquationsAt[S,later,ordered] j ≠ 0 :=
  segmentEquations_ne_zero _ _ _ j

open Classical in
/-- Keep the original whole-face boundaries together with every prescribed cut segment. -/
def compatibleMeshProcessedComparisonFullEquations (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    (({p // p ∈ PairsAt[S,later]} × Fin 3) ⊕ ((T).Index × Fin 3)) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim EquationsAt[S,later,ordered] (Q).originalEdgeEquations

local notation "FullEquationsAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonFullEquations compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h

open Classical in
theorem compatibleMeshProcessedComparisonFullEquations_ne_zero
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) (j) :
    FullEquationsAt[S,later,ordered] j ≠ 0 := by
  cases j with
  | inl j =>
      exact K.compatibleMeshProcessedComparisonEquations_ne_zero compact nonempty R
        no_boundary level higher M positive inner_disk beta acute S later ordered j
  | inr j => exact (Q).originalEdgeEquations_ne_zero j

open Classical in
/-- Construct the full physical refinement, preserving every original face boundary. -/
def compatibleMeshProcessedComparisonRefinementMesh (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    SpatialEnvelope.ConstrainedTriangulation M.plane FullEquationsAt[S,later,ordered] (-later) :=
  M.mesh _ (K.compatibleMeshProcessedComparisonFullEquations_ne_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S later ordered) positive inner_disk
    (q := R.cutInteriorPoint) (by
      have bound := R.cutInteriorPoint_height level higher
      linarith)

open Classical in
/-- Construct the larger actual conforming mesh of the same original whole roof. -/
def compatibleMeshProcessedComparisonMesh (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    SpatialEnvelope.ConstrainedTriangulation M.plane EquationsAt[S,later,ordered] (-later) :=
  (K.compatibleMeshProcessedComparisonRefinementMesh compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S later ordered).selectConstraints
      EquationsAt[S,later,ordered] Sum.inl (fun _ => rfl)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h

open Classical in
local instance processedComparisonNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

open Classical in
/-- The larger comparison mesh is conforming by its actual constrained construction. -/
theorem compatibleMeshProcessedComparisonMesh_conforming (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    TriangleFamily.Conforming (NewAt[S,later,ordered]).projectedTriangle :=
  M.mesh_conforming _ (K.compatibleMeshProcessedComparisonFullEquations_ne_zero compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered)
    positive inner_disk (by
      have bound := R.cutInteriorPoint_height level higher
      linarith)

open Classical in
/-- Touching the original partial cut at a regular new edge point cuts that whole new edge.
The finite segment constraints and the exact original cut-window agreement derive this. -/
theorem compatibleMeshProcessedComparisonMesh_cut_aligned (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (f : (NewAt[S,later,ordered]).Index) (e : Fin 3)
    (x : ((NewAt[S,later,ordered]).projectedTriangle f).Edge e)
    (regular : ¬ ((NewAt[S,later,ordered]).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ CutsAt[S]) :
    ((NewAt[S,later,ordered]).projectedTriangle f).edge e ⊆ CutsAt[S] := by
  have in_clip (p : Plane)
      (on_edge : p ∈ ((NewAt[S,later,ordered]).projectedTriangle f).edge e) :
      p ∈ SpatialEnvelope.clip M.plane (-later) :=
    (NewAt[S,later,ordered]).cover.symm.subset (Set.mem_iUnion.mpr
      ⟨f, ((NewAt[S,later,ordered]).projectedTriangle f).edge_subset e on_edge⟩)
  have finite_member := (K.compatibleMeshProcessedWindowCarrier_agree compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S ordered.le
    (in_clip x.val x.property)).mp member
  rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs] at finite_member
  have aligned := (NewAt[S,later,ordered]).prescribed_cut_aligned
    (fun p : {p // p ∈ PairsAt[S,later]} => p.val.1) (fun p => p.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ordered) f e x regular finite_member
  intro p on_edge
  apply (K.compatibleMeshProcessedWindowCarrier_agree compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S ordered.le (in_clip p on_edge)).mpr
  rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs]
  exact aligned on_edge

open Classical in
/-- The original partial cut avoids every new comparison face interior. -/
theorem compatibleMeshProcessedComparisonMesh_cut_disjoint_interior
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (f : (NewAt[S,later,ordered]).Index) :
    Disjoint (interior ((NewAt[S,later,ordered]).projectedTriangle f).carrier) CutsAt[S] := by
  apply Set.disjoint_left.mpr
  intro p in_triangle member
  have in_clip := (NewAt[S,later,ordered]).cover.symm.subset
    (Set.mem_iUnion.mpr ⟨f, interior_subset in_triangle⟩)
  have finite_member := (K.compatibleMeshProcessedWindowCarrier_agree compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S ordered.le in_clip).mp member
  rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs] at finite_member
  exact Set.disjoint_left.mp ((NewAt[S,later,ordered]).prescribed_cut_disjoint_interior
    (fun p : {p // p ∈ PairsAt[S,later]} => p.val.1) (fun p => p.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ordered) f) in_triangle finite_member

open Classical in
/-- The larger retained triangle complex has exactly the same original graph-patch cut metric,
including all bank and corner copies. No new processing stage or forest is substituted. -/
def compatibleMeshProcessedComparisonGraphEquiv (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) :
    (NewAt[S,later,ordered]).pairedComplex.Realization
      ((NewAt[S,later,ordered]).toTriangulation.retainOutside CutsAt[S]) ≃ᵢ
        (NewAt[S,later,ordered]).toTriangulation.graphPartition.Cut CutsAt[S] :=
  (NewAt[S,later,ordered]).toTriangulation.alignedCutGraphEquiv
    (K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered) CutsAt[S]
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered)

end Unfoldings.ConvexRoof
