module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankMetric
public import Unfoldings.Roof.SpatialEnvelopeCutBoundaryFibers
public import Unfoldings.Complex.BoundaryContourPaths

/-! Constructed finite terminal banks lie on the actual original intrinsic cut boundary. -/

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

local instance finiteTerminalBoundaryIndexFintype : Fintype (T).Index :=
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

local instance finiteTerminalBoundaryWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- Construct the original finite cut boundary contour from its actual cut-disk topology. -/
def compatibleMeshBoundaryContour : (T).pairedComplex.BoundaryContour (Fcut).retain :=
  (T).pairedComplex.boundaryContourOfConnected (Fcut).retain
    ((T).pairedFolding.boundaryGraph_connected_of_disk (Fcut).retain (Fcut).cutDisk)

/-- Every point of the constructed finite terminal bank belongs to the actual
intrinsic bank boundary, including its original source and truncation endpoint copies. -/
theorem compatibleMeshTerminalBank_mem_boundary (t : Set.Icc (0 : ℝ) τ) :
    K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W r side t ∈ (T).pairedComplex.bankBoundary (Fcut).retain := by
  let x := K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side t
  have position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x) =
      R.exterior.ray (R.terminalIndex r) t.val :=
    (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side t)).trans
      (SpatialEnvelope.horizontal_point M.plane _)
  by_cases before : t.val < τ
  · have below := (R.terminal_ray_below_iff level higher r t.property.1).mpr before
    have in_cut : R.exterior.ray (R.terminalIndex r) t.val ∈ R.truncatedCarrier level higher :=
      (R.mem_truncatedCarrier_iff level higher below.le).mpr
        (Or.inr (Set.mem_iUnion.mpr ⟨r, t.val, t.property.1, rfl⟩))
    have internal : R.exterior.ray (R.terminalIndex r) t.val ∈
        interior (SpatialEnvelope.clip M.plane (-level)) := by
      rw [M.clip_eq_sublevel, neg_neg]
      exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
    obtain ⟨s, not_kept, on_edge⟩ := K.compatibleCutMesh_cut_seam compact nonempty R no_boundary
      level higher M positive inner_disk in_cut internal
    have removed_full : s ∉ (Fcut).retain := by
      rwa [K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher M
        positive inner_disk beta acute]
    let q := ((T).edgeProjection ((T).pairedComplex.left s).face
      ((T).pairedComplex.left s).edge).symm
      ⟨R.exterior.ray (R.terminalIndex r) t.val, on_edge⟩
    have projected :
        Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face q.val) =
          R.exterior.ray (R.terminalIndex r) t.val :=
      ((M.plane ((T).support ((T).pairedComplex.left s).face)).horizontal_place q.val).trans
        ((M.plane ((T).support ((T).pairedComplex.left s).face)).project.apply_symm_apply _)
    exact (T).toTriangulation.mem_bankBoundary_of_projected_cut_edge conforming (Fcut).retain s
      removed_full q x (position.trans projected.symm)
  · have endpoint : t.val = τ := le_antisymm t.property.2 (not_lt.mp before)
    let included := Set.subset_univ (Fcut).retain
    have projected : Cap.horizontal ((T).pairedFolding.toSpace Set.univ
        ((T).pairedComplex.forgetCuts included x)) = R.terminalPoint level r :=
      (congrArg Cap.horizontal ((T).pairedFolding.toSpace_forgetCuts included x)).trans
        (position.trans (congrArg (R.exterior.ray (R.terminalIndex r)) endpoint))
    have on_rim : R.terminalPoint level r ∈ frontier (Q).footprint := by
      rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel, neg_neg]
      exact R.terminalPoint_mem_frontier level higher r
    apply (T).pairedComplex.bankBoundary_preimage_forgetCuts included
    apply ((Q).projected_mem_frontier_iff_bankBoundary _).mp
    exact Eq.mpr (congrArg (fun p : Plane => p ∈ frontier (Q).footprint) projected) on_rim

/-- Every constructed finite terminal-bank point occurs on an original directed bank. -/
theorem exists_directedBank_at_compatibleMeshTerminalBank
    (contour : (T).pairedComplex.BoundaryContour (Fcut).retain) (t : Set.Icc (0 : ℝ) τ) :
    ∃ (i : Fin (contour.length + 1)) (u : unitInterval),
      (T).pairedComplex.directedBoundaryPath (contour.cycle.point i) u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side t :=
  TriangleComplex.BoundaryContour.exists_directedBoundaryPath (T).pairedComplex contour
    (K.compatibleMeshTerminalBank_mem_boundary compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side t)

/-- Locate every finite terminal-bank copy on the constructed original cut contour.
The contour, intrinsic boundary membership and endpoint copies are all derived. -/
theorem exists_originalDirectedBank_at_compatibleMeshTerminalBank (t : Set.Icc (0 : ℝ) τ) :
    ∃ (i : Fin ((K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher M
        positive inner_disk beta acute).length + 1)) (u : unitInterval),
      (T).pairedComplex.directedBoundaryPath
        ((K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher M positive
          inner_disk beta acute).cycle.point i) u =
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side t :=
  K.exists_directedBank_at_compatibleMeshTerminalBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side
    (K.compatibleMeshBoundaryContour compact nonempty R no_boundary level higher M positive
      inner_disk beta acute) t

end Unfoldings.ConvexRoof
