module

public import Unfoldings.Roof.CompatibleMeshPhysicalCut
public import Unfoldings.Roof.SpatialEnvelopeProjectedRemovedSeams
public import Unfoldings.Roof.CompatiblePartialCutPartitionIndependence
public import Unfoldings.Complex.ProcessedParentCuts
public import Unfoldings.Roof.OpenSeamInterior
public import Unfoldings.Roof.TruncatedCutEnds

/-! Construct actual intermediate closed cuts on the whole roof from original processing stages. -/

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

local instance processedWholeCarrierIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

/-- Keep all original outer tails and precisely the finite original seams already processed.
The actual original mesh determines the partial whole-roof cut. -/
def compatibleMeshProcessedCarrier (S : (Fcut).parents.ParentFrontier) : Set Plane :=
  (R.carrier ∩ {p | level ≤ (K.clippedExtension slopes compact nonempty).height p}) ∪
    (Q).removedProjectedSeamCarrier RetainAt[S]

/-- Every actual intermediate whole-roof cut is closed, including all its endpoint copies. -/
theorem isClosed_compatibleMeshProcessedCarrier (S : (Fcut).parents.ParentFrontier) :
    IsClosed (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) :=
  (R.isClosed_carrier.inter (isClosed_le continuous_const
    (K.clippedExtension slopes compact nonempty).continuous_height)).union
    ((Q).isClosed_removedProjectedSeamCarrier _)

/-- Intermediate whole cuts contain only actual original forest points. -/
theorem compatibleMeshProcessedCarrier_subset (S : (Fcut).parents.ParentFrontier) :
    K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ⊆ R.carrier := by
  intro p member
  rcases member with outside | finite
  · exact outside.1
  · have included := (Q).removedProjectedSeamCarrier_antitone
      ((T).pairedComplex.selectedRetain_subset_processed (Fcut).selection S)
    obtain ⟨z, on_removed, rfl⟩ := included finite
    obtain ⟨s, x, on_edge, rfl⟩ := Set.mem_iUnion.mp on_removed
    exact K.compatibleMesh_removed_edge compact nonempty R no_boundary level higher M positive
      inner_disk beta acute s.val s.property ⟨x, on_edge⟩

/-- Processing more vertices only adds actual cut points on the whole roof. -/
theorem compatibleMeshProcessedCarrier_mono {S U : (Fcut).parents.ParentFrontier}
    (more : S.processed ⊆ U.processed) :
    K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ⊆
        K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
          inner_disk beta acute U := by
  intro p member
  rcases member with outside | finite
  · exact Or.inl outside
  · exact Or.inr ((Q).removedProjectedSeamCarrier_antitone
      ((T).pairedComplex.processedParentRetain_antitone (Fcut).selection more) finite)

/-- Initially only the actual outer tails are cut; unused marked roots add no finite cut. -/
theorem compatibleMeshProcessedCarrier_initial :
    K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute (Fcut).parents.initialFrontier =
        R.carrier ∩ {p | level ≤ (K.clippedExtension slopes compact nonempty).height p} := by
  rw [compatibleMeshProcessedCarrier, TriangleComplex.processedParentRetain_initial,
    ConvexRoof.removedProjectedSeamCarrier_univ, Set.union_empty]

/-- Inside the strict truncation sublevel, the cut is exactly the removed original seams. -/
theorem mem_compatibleMeshProcessedCarrier_inside (S : (Fcut).parents.ParentFrontier)
    {p : Plane} (below : (K.clippedExtension slopes compact nonempty).height p < level) :
    p ∈ K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ↔ p ∈ (Q).removedProjectedSeamCarrier RetainAt[S] := by
  change (_ ∧ level ≤ _) ∨ _ ↔ _
  simp only [not_le.mpr below, and_false, false_or]

/-- The original outer tails are present unchanged at every processing stage. -/
theorem mem_compatibleMeshProcessedCarrier_outside (S : (Fcut).parents.ParentFrontier)
    {p : Plane} (above : level ≤ (K.clippedExtension slopes compact nonempty).height p) :
    p ∈ K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ↔ p ∈ R.carrier :=
  ⟨fun member => K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level
    higher M
      positive inner_disk beta acute S member,
    fun member => Or.inl ⟨member, above⟩⟩

/-- Once every original selector is processed, the actual whole carrier is exactly
all of the original forest, including every finite edge and unbounded terminal ray. -/
theorem compatibleMeshProcessedCarrier_final (S : (Fcut).parents.ParentFrontier)
    (all : S.processed = Set.univ) :
    K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S = R.carrier := by
  apply Set.Subset.antisymm
    (K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)
  intro p member
  by_cases above : level ≤ (K.clippedExtension slopes compact nonempty).height p
  · exact Or.inl ⟨member, above⟩
  · have below := lt_of_not_ge above
    have on_finite := (R.mem_truncatedCarrier_iff level higher below.le).mpr member
    have in_clip : p ∈ interior (SpatialEnvelope.clip M.plane (-level)) := by
      rw [M.clip_eq_sublevel, neg_neg]
      exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
    obtain ⟨seam, removed, on_edge⟩ := K.compatibleCutMesh_cut_seam compact nonempty R no_boundary
      level higher M positive inner_disk on_finite in_clip
    have selected : seam ∉ (Fcut).retain := by
      rwa [K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher M
        positive inner_disk beta acute]
    have current : seam ∉ RetainAt[S] := by
      rwa [(T).pairedComplex.processedParentRetain_eq_selected (Fcut).selection S all]
    let f := ((T).pairedComplex.left seam).face
    let e := ((T).pairedComplex.left seam).edge
    let x := ((T).toTriangulation.edgeProjection f e).symm ⟨p, on_edge⟩
    refine Or.inr ⟨(T).placement f x.val,
      (T).pairedFolding.removed_edge_mem_removedSeamCarrier RetainAt[S] seam current x, ?_⟩
    exact ((M.plane ((T).support f)).horizontal_place x.val).trans
      (congrArg Subtype.val (((T).toTriangulation.edgeProjection f e).apply_symm_apply ⟨p,
        on_edge⟩))

/-- Actual open original paired seams never meet any of the fixed outer tails. -/
theorem compatibleMesh_openSeam_disjoint_outer (s : (T).pairedComplex.Seam) :
    Disjoint ((T).pairedFolding.openSeamImage s)
      (Cap.horizontal ⁻¹' (R.carrier ∩
        {p | level ≤ (K.clippedExtension slopes compact nonempty).height p})) := by
  apply Set.disjoint_left.mpr
  intro z on_open on_outer
  have in_footprint := (Q).horizontal_openSeamImage_mem_interior s on_open
  rw [(T).toTriangulation.roof_footprint conforming inside,
    M.clip_eq_sublevel, neg_neg] at in_footprint
  have bounded := interior_subset in_footprint
  have on_finite := (R.mem_truncatedCarrier_iff level higher bounded).mpr on_outer.1
  rcases R.truncatedCarrier_strict_or_terminalPoint level higher on_finite with below | terminal
  · exact (not_lt_of_ge on_outer.2) below
  · obtain ⟨root, same⟩ := terminal
    exact (R.terminalPoint_mem_frontier level higher root).2 (same ▸ in_footprint)

/-- The retained open current seams avoid the entire actual intermediate whole cut. -/
theorem compatibleMeshProcessed_retained_open_edge (S : (Fcut).parents.ParentFrontier)
    (s : (T).pairedComplex.Seam) (kept : s ∈ RetainAt[S]) :
    Disjoint ((T).pairedFolding.openSeamImage s)
      (Cap.horizontal ⁻¹' K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level
        higher M positive inner_disk beta acute S) := by
  apply Set.disjoint_left.mpr
  intro z on_open on_cut
  rcases on_cut with outer | finite
  · exact Set.disjoint_left.mp (K.compatibleMesh_openSeam_disjoint_outer compact nonempty R
      no_boundary level higher M positive inner_disk s) on_open outer
  · exact Set.disjoint_left.mp
      ((Q).openSeamImage_disjoint_projected_removed RetainAt[S] s kept) on_open finite

/-- Every removed original closed current edge lies in the actual intermediate whole cut. -/
theorem compatibleMeshProcessed_removed_edge (S : (Fcut).parents.ParentFrontier)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (x : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) :
    Cap.horizontal ((T).placement ((T).pairedComplex.left s).face x.val) ∈
      K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S :=
  Or.inr ((Q).removed_edge_mem_projected_removed RetainAt[S] s removed x)

/-- The actual current finite retained complex is isometric to the original graph patch
cut by the actual intermediate whole-roof carrier, with no bank-copy certificate supplied. -/
def compatibleMeshProcessedGraphEquiv (S : (Fcut).parents.ParentFrontier) :
    (T).pairedComplex.Realization RetainAt[S] ≃ᵢ
      (T).toTriangulation.graphPartition.Cut
        (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
          inner_disk beta acute S) :=
  (T).toTriangulation.pairedCutGraphEquiv conforming RetainAt[S] _
    (K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessed_retained_open_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S)

/-- The whole original spatial folding survives the intermediate metric identification. -/
theorem fold_compatibleMeshProcessedGraphEquiv (S : (Fcut).parents.ParentFrontier)
    (x : (T).pairedComplex.Realization RetainAt[S]) :
    (T).toTriangulation.graphPartition.fold
      (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S)
      (K.compatibleMeshProcessedGraphEquiv compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S x) = (T).pairedFolding.toSpace RetainAt[S] x :=
  (T).toTriangulation.fold_pairedCutGraphEquiv conforming RetainAt[S] _
    (K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessed_retained_open_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) x

variable (W V : R.WholeCutModel M)

local instance processedWholeLeftIndexFintype : Fintype W.Index := W.finiteIndex
local instance processedWholeRightIndexFintype : Fintype V.Index := V.finiteIndex

/-- The actual intermediate whole cut has a complete intrinsic metric. -/
theorem compatibleMeshProcessedCut_complete (S : (Fcut).parents.ParentFrontier) :
    CompleteSpace (W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S)) := W.partition.cut_complete _

/-- Changing the retained whole-roof partition preserves the intermediate actual metric. -/
def compatibleMeshProcessedCutEquiv (S : (Fcut).parents.ParentFrontier) :
    W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) ≃ᵢ
    V.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) :=
  W.partialCutModelEquiv V _
    (K.isClosed_compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)

/-- The model change preserves the original whole-roof spatial point at every stage. -/
theorem restore_compatibleMeshProcessedCutEquiv (S : (Fcut).parents.ParentFrontier)
    (x : W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S)) :
    V.partition.restoreCut
      (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S)
      (K.compatibleMeshProcessedCutEquiv compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W V S x) =
    W.partition.restoreCut
      (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S) x :=
  W.restore_partialCutModelEquiv V _
    (K.isClosed_compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S) x

/-- Restoring a later processing stage to an earlier one retains the actual whole-roof copies. -/
def compatibleMeshForgetProcessedCut {S U : (Fcut).parents.ParentFrontier}
    (more : S.processed ⊆ U.processed) :
    W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute U) →
    W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) :=
  W.partition.forgetCut _ _ (K.compatibleMeshProcessedCarrier_mono compact nonempty R no_boundary
    level higher M positive inner_disk beta acute more)

/-- Restoration between actual processing stages is nonexpanding. -/
theorem compatibleMeshForgetProcessedCut_lipschitz {S U : (Fcut).parents.ParentFrontier}
    (more : S.processed ⊆ U.processed) :
    LipschitzWith 1 (K.compatibleMeshForgetProcessedCut compact nonempty R no_boundary level
      higher M
      positive inner_disk beta acute W more) :=
  W.partition.forgetCut_lipschitz _ _
    (K.compatibleMeshProcessedCarrier_mono compact nonempty R no_boundary level higher M positive
      inner_disk beta acute more)

/-- Restoring a processing stage preserves the original spatial roof point exactly. -/
theorem restore_compatibleMeshForgetProcessedCut {S U : (Fcut).parents.ParentFrontier}
    (more : S.processed ⊆ U.processed)
    (x : W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level
      higher M positive inner_disk beta acute U)) :
    W.partition.restoreCut
      (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S)
      (K.compatibleMeshForgetProcessedCut compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W more x) =
    W.partition.restoreCut
      (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute U) x :=
  W.partition.restoreCut_forgetCut _ _
    (K.compatibleMeshProcessedCarrier_mono compact nonempty R no_boundary level higher M positive
      inner_disk beta acute more) x

/-- Restoring processing stages commutes with changing the original whole-roof partition. -/
theorem compatibleMeshProcessedCutEquiv_forget {S U : (Fcut).parents.ParentFrontier}
    (more : S.processed ⊆ U.processed)
    (x : W.partition.Cut (K.compatibleMeshProcessedCarrier compact nonempty R no_boundary level
      higher M positive inner_disk beta acute U)) :
    K.compatibleMeshForgetProcessedCut compact nonempty R no_boundary level higher M positive
      inner_disk beta acute V more
      (K.compatibleMeshProcessedCutEquiv compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W V U x) =
    K.compatibleMeshProcessedCutEquiv compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W V S
      (K.compatibleMeshForgetProcessedCut compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W more x) :=
  W.partialCutModelEquiv_forgetCut V _ _
    (K.isClosed_compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute U)
    (K.isClosed_compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level higher M positive
      inner_disk beta acute U)
    (K.compatibleMeshProcessedCarrier_mono compact nonempty R no_boundary level higher M positive
      inner_disk beta acute more) x

end Unfoldings.ConvexRoof
