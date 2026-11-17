module

public import Unfoldings.Roof.CompatibleProcessedTerminalBanks
public import Unfoldings.Topology.TwoClosedLifts

/-! Connected outer curves follow a single original bank in every intermediate cut. -/

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

local instance processedTerminalMatchingIndexFintype : Fintype (T).Index :=
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
variable (W : R.WholeCutModel M)

local instance processedTerminalMatchingWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S

local notation "BankAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side

/-- A continuous connected outer curve cannot change its original terminal-bank side,
even at fine subdivision vertices. Earlier restored cuts may merge the two banks. -/
theorem compatibleMeshProcessed_terminalBank_side_constant
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (S : (Fcut).parents.ParentFrontier) (r : {v // v ∈ R.parents.roots})
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (time : A → ℝ≥0) (after : ∀ a, R.terminalTime level r < (time a).val)
    (position : ∀ a, Cap.horizontal (W.partition.restoreCut CutsAt[S] (curve a)).val =
      R.exterior.ray (R.terminalIndex r) (time a).val) :
    ∃ side : Bool, ∀ a, curve a = BankAt[S,r,side] (time a) := by
  apply exists_fixed_bool_lift curve continuous_curve (fun side => BankAt[S,r,side])
    (fun side => (K.restoredWholeTerminalBank_isClosedEmbedding compact nonempty R no_boundary W
      CutsAt[S] IncludedAt[S] r side).isClosed_range) time
  · intro x
    exact K.exists_restoredWholeTerminalBank_side compact nonempty R no_boundary W CutsAt[S]
      IncludedAt[S] r (time x) ((R.terminalTime_pos level higher r).trans (after x))
      (curve x) (position x)
  · intro x side other different t
    exact K.compatibleMeshProcessed_terminalBank_ne compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S r side other different (time x) t (after x)

/-- Matching on a connected dense outer portion also fixes the actual endpoint copies,
including the old truncation junction where the two restored banks may meet. -/
theorem compatibleMeshProcessed_terminalBank_side_of_dense_after
    {A : Type*} [TopologicalSpace A]
    (S : (Fcut).parents.ParentFrontier) (r : {v // v ∈ R.parents.roots})
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (time : A → ℝ≥0) (continuous_time : Continuous time) (portion : Set A)
    (connected : IsPreconnected portion) (dense : Dense portion)
    (after : ∀ a ∈ portion, R.terminalTime level r < (time a).val)
    (position : ∀ a, Cap.horizontal (W.partition.restoreCut CutsAt[S] (curve a)).val =
      R.exterior.ray (R.terminalIndex r) (time a).val) :
    ∃ side : Bool, ∀ a, curve a = BankAt[S,r,side] (time a) := by
  let : PreconnectedSpace portion := Subtype.preconnectedSpace connected
  obtain ⟨side, same⟩ := K.compatibleMeshProcessed_terminalBank_side_constant compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S r
    (fun a : portion => curve a.val) (continuous_curve.comp continuous_subtype_val)
    (fun a : portion => time a.val) (fun a => after a.val a.property) (fun a => position a.val)
  have agrees : Set.EqOn curve (fun a => BankAt[S,r,side] (time a)) portion :=
    fun a member => same ⟨a, member⟩
  exact ⟨side, fun a => agrees.closure continuous_curve
    ((Dilation.lipschitzWith
      (K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
        r side)).continuous.comp continuous_time) (dense a)⟩

end Unfoldings.ConvexRoof
