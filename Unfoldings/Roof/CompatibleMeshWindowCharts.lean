module

public import Unfoldings.Roof.CompatibleMeshPhysicalCut
public import Unfoldings.Roof.CompatibleLevelWindow
public import Unfoldings.Roof.CompatibleWindowPairedMesh

/-! Construct whole original-bank charts from the actual finite compatible forest mesh. -/

@[expose] public section

noncomputable section

open scoped ENNReal

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

local instance compatibleMeshWindowIndexFintype : Fintype (T).Index :=
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

local instance compatibleMeshWindowWholeFintype : Fintype W.Index := W.finiteIndex

/-- Include the actual constructed finite forest-cut complex in any original whole-cut model. -/
@[macro_inline] def compatibleMeshWholeMap (y : (T).pairedComplex.Realization (Fcut).retain) :
    W.Cut :=
  (V).pairedMeshMap proper full (T).toTriangulation domain heights outside W conforming
    (Fcut).retain removed retained y

/-- Every original bank copy strictly below the completion level has a whole intrinsic ball
in the actual finite forest-cut triangle complex. All mesh, metric and seam data are constructed. -/
theorem exists_compatibleMesh_ball_chart (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level) :
    ∃ source : (T).pairedComplex.Realization (Fcut).retain,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W z.val := by
  apply (V).exists_pairedMesh_ball_chart proper full (T).toTriangulation domain heights outside
    W conforming (Fcut).retain removed retained x
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

/-- Finite comparison charts preserve each original spatial bank point. -/
theorem restore_compatibleMeshWholeMap (y : (T).pairedComplex.Realization (Fcut).retain) :
    (W.partition.restoreCut R.carrier
      (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W y)).val = (T).pairedFolding.toSpace (Fcut).retain y :=
  (V).restore_pairedMeshMap proper full (T).toTriangulation domain heights outside W conforming
    (Fcut).retain removed retained y

theorem compatibleMeshWholeMap_lipschitz : LipschitzWith 1
    (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W) :=
  (V).pairedMeshMap_lipschitz proper full (T).toTriangulation domain heights outside W conforming
    (Fcut).retain removed retained

end Unfoldings.ConvexRoof
