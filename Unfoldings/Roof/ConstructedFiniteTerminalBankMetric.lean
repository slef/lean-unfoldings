module

public import Unfoldings.Roof.ConstructedFiniteTerminalBanks

/-! Original finite terminal banks retain exact distances, spatial points and separated copies. -/

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

local instance constructedTerminalMetricIndexFintype : Fintype (T).Index :=
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

local instance constructedTerminalMetricWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- Every pair of original finite-bank points has precisely its whole-bank distance. -/
theorem edist_compatibleMeshTerminalBank (s t : Set.Icc (0 : ℝ) τ) :
    edist (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side s)
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side t) =
      edist (bank ⟨s.val, s.property.1⟩) (bank ⟨t.val, t.property.1⟩) := by
  have first := K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher
    M positive inner_disk beta acute W r side s
  have last := K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher
    M positive inner_disk beta acute W r side t
  apply le_antisymm
  · exact (K.compatibleMeshTerminalBank_lipschitz compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side s t).trans_eq
      (Dilation.edist_eq bank ⟨s.val, s.property.1⟩ ⟨t.val, t.property.1⟩).symm
  · have bound := K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side s)
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side t)
    exact (congrArg₂ edist first last).symm.trans_le (bound.trans_eq (one_mul _))

/-- A constructed finite terminal bank is an embedded interval with its actual spatial speed. -/
def compatibleMeshTerminalBankDilation : Set.Icc (0 : ℝ) τ →ᵈ
    (T).pairedComplex.Realization (Fcut).retain :=
  dilationOfIsometricLift bank (fun t : Set.Icc (0 : ℝ) τ => ⟨t.val, t.property.1⟩)
    (fun _ _ => rfl)
    (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
    (K.edist_compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)

theorem compatibleMeshTerminalBank_isClosedEmbedding : Topology.IsClosedEmbedding
    (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) := by
  let : CompleteSpace (Set.Icc (0 : ℝ) τ) := isClosed_Icc.isComplete.completeSpace_coe
  exact Dilation.isClosedEmbedding (K.compatibleMeshTerminalBankDilation compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side)

/-- Each constructed finite bank point retains its literal original spatial roof point. -/
theorem fold_compatibleMeshTerminalBank (t : Set.Icc (0 : ℝ) τ) :
    (T).pairedFolding.toSpace (Fcut).retain
      (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side t) =
          SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) :=
  (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W _).symm.trans
    ((congrArg (fun x => (W.partition.restoreCut R.carrier x).val)
      (K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side t)).trans
        (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side _))

/-- Opposite finite banks retain distinct actual copies at every positive parameter,
including their original finite truncation endpoints. -/
theorem compatibleMeshTerminalBank_ne (other : Bool) (different : side ≠ other)
    (s t : Set.Icc (0 : ℝ) τ) (spos : 0 < s.val) :
    K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side s ≠
        K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r other t := by
  intro equal
  apply K.wholeTerminalBank_ne compact nonempty R no_boundary W r side other different
    ⟨s.val, s.property.1⟩ ⟨t.val, t.property.1⟩ spos
  exact (K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side s).symm.trans
    ((congrArg (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W) equal).trans
      (K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r other t))

end Unfoldings.ConvexRoof
