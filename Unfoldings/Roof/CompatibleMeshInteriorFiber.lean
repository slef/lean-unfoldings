module

public import Unfoldings.Roof.CompatibleMeshCornerCharts
public import Unfoldings.Roof.CompatibleWindowPairedFiber

/-! Construct unique finite comparison copies of every original bank below the completion level. -/

@[expose] public section

noncomputable section

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

local instance compatibleFiberIndexFintype : Fintype (T).Index :=
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

local instance compatibleFiberWholeFintype : Fintype W.Index := W.finiteIndex

/-- The actual finite forest inclusion preserves the whole fiber at an original interior copy. -/
theorem compatibleMeshWholeMap_injective_at (x : (T).pairedComplex.Realization (Fcut).retain)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x)) < level)
    (y : (T).pairedComplex.Realization (Fcut).retain)
    (equal : K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W x =
        K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W y) : x = y := by
  have window_positive : ∀ i, 0 < SpatialEnvelope.levelEquation M.plane (-level) i
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x)) := by
    apply SpatialEnvelope.levelEquation_positive
    rw [M.height_eq]
    linarith
  exact (V).pairedMeshMap_injective_at proper full (T).toTriangulation domain heights outside
    W conforming (Fcut).retain removed retained x window_positive y equal

/-- Every original whole-cut copy below the level has exactly one actual finite-mesh copy. -/
theorem existsUnique_compatibleMesh_preimage (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level) :
    ∃! y : (T).pairedComplex.Realization (Fcut).retain,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W y = x := by
  obtain ⟨y, image, _chart⟩ := K.exists_compatibleMesh_ball_chart compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W x below
  have physical : (T).pairedFolding.toSpace (Fcut).retain y =
      (W.partition.restoreCut R.carrier x).val :=
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W y).symm.trans
      (congrArg (fun z => (W.partition.restoreCut R.carrier z).val) image)
  have source_below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain y)) < level :=
    Eq.mpr (congrArg (fun p : Space =>
      (K.clippedExtension slopes compact nonempty).height (Cap.horizontal p) < level)
        physical) below
  refine ⟨y, image, fun z hz => ?_⟩
  exact (K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W y source_below z (image.trans hz.symm)).symm

/-- The uniquely determined actual finite copy, chosen only after its existence is proved. -/
def compatibleMeshLift (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level) :
    (T).pairedComplex.Realization (Fcut).retain :=
  (K.existsUnique_compatibleMesh_preimage compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W x below).choose

@[simp] theorem compatibleMeshWholeMap_lift (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level) :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W (K.compatibleMeshLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W x below) = x :=
  (K.existsUnique_compatibleMesh_preimage compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W x below).choose_spec.1

theorem compatibleMeshLift_unique (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level)
    (y : (T).pairedComplex.Realization (Fcut).retain)
    (image : K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W y = x) :
    y = K.compatibleMeshLift compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W x below :=
  (K.existsUnique_compatibleMesh_preimage compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W x below).choose_spec.2 y image

end Unfoldings.ConvexRoof
