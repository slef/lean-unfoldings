module

public import Unfoldings.Roof.CompatibleProcessedComparisonCharts
public import Unfoldings.Topology.ImageRange

/-! Every finite original intermediate-cut path lifts to an actual larger comparison mesh. -/

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

local instance processedComparisonPathIndexFintype : Fintype (T).Index :=
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
local instance processedComparisonPathNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance processedComparisonPathWholeFintype : Fintype W.Index := W.finiteIndex

open Classical in
/-- Lift an entire original path to its actual larger-window copies. Endpoints are the
canonical lifts, and continuity follows from whole metric charts and unique fibers. -/
def compatibleMeshProcessedComparisonPathLift
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    {a b : W.partition.Cut CutsAt[S]} (P : Path a b)
    (below : ∀ t, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) < later) :
    Path
      (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered (P 0) (below 0))
      (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered (P 1) (below 1)) where
  toFun t := K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered (P t) (below t)
  continuous_toFun := by
    have positive_path : ∀ (t : unitInterval) j,
        0 < SpatialEnvelope.levelEquation M.plane (-later) j
          (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) := by
      intro t
      apply SpatialEnvelope.levelEquation_positive
      rw [M.height_eq]
      linarith [below t]
    change Continuous ((VAt[later,ordered]).partialPairedMeshCurveLift ProperAt[later,ordered]
      FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights
      CutsAt[S] ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
      NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
      (Set.Icc (0 : ℝ) 1) P positive_path)
    exact (VAt[later,ordered]).partialPairedMeshCurveLift_continuous ProperAt[later,ordered]
      FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights
      CutsAt[S] ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
      NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
      (Set.Icc (0 : ℝ) 1) P positive_path P.continuous
  source' := rfl
  target' := rfl

open Classical in
/-- The lifted path retains every literal original whole-cut point in order. -/
theorem compatibleMeshProcessedComparisonWholeMap_pathLift
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    {a b : W.partition.Cut CutsAt[S]} (P : Path a b)
    (below : ∀ t, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) < later) (t : unitInterval) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered
      (K.compatibleMeshProcessedComparisonPathLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered P below t) = P t :=
  K.compatibleMeshProcessedComparisonWholeMap_lift compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered (P t) (below t)

open Classical in
/-- The entire original path carrier, including endpoint copies, survives larger-window lifting. -/
theorem compatibleMeshProcessedComparisonPathLift_range
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    {a b : W.partition.Cut CutsAt[S]} (P : Path a b)
    (below : ∀ t, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) < later) :
    (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered) ''
      Set.range (K.compatibleMeshProcessedComparisonPathLift compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered P below) = Set.range P := by
  exact image_range_eq_of_pointwise _ _ P
    (K.compatibleMeshProcessedComparisonWholeMap_pathLift compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered P below)

open Classical in
/-- Any original finite whole-cut path fits in an actually constructed larger comparison mesh.
The level is derived from its compact image, with no supplied height or metric certificate. -/
theorem exists_compatibleMeshProcessedComparison_path
    (S : (Fcut).parents.ParentFrontier) {a b : W.partition.Cut CutsAt[S]} (P : Path a b) :
    ∃ later : ℝ, ∃ ordered : level < later,
      ∃ below : ∀ t, (K.clippedExtension slopes compact nonempty).height
          (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) < later,
        ∃ Pfine : Path
            (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
              positive inner_disk beta acute W S later ordered (P 0) (below 0))
            (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
              positive inner_disk beta acute W S later ordered (P 1) (below 1)),
          ∀ t, K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
            higher M positive inner_disk beta acute W S later ordered (Pfine t) = P t := by
  have continuous_height : Continuous (fun t : unitInterval =>
      (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val)) :=
    (K.clippedExtension slopes compact nonempty).continuous_height.comp
      (Cap.horizontalCLM.continuous.comp (PolygonalPoint.ambient_lipschitz.continuous.comp
        ((W.partition.restoreCut_lipschitz CutsAt[S]).continuous.comp P.continuous)))
  obtain ⟨bound, bounded⟩ := (isCompact_range continuous_height).bddAbove
  let later := max level bound + 1
  have ordered : level < later := (le_max_left _ _).trans_lt (lt_add_one _)
  have below : ∀ t, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (P t)).val) < later := fun t =>
    (bounded (Set.mem_range_self t)).trans_lt ((le_max_right _ _).trans_lt (lt_add_one _))
  exact ⟨later, ordered, below,
    K.compatibleMeshProcessedComparisonPathLift compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered P below,
    K.compatibleMeshProcessedComparisonWholeMap_pathLift compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered P below⟩

end Unfoldings.ConvexRoof
