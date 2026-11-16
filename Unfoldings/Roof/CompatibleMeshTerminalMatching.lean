module

public import Unfoldings.Roof.CompatibleMeshWindowCharts
public import Unfoldings.Roof.CompatibleTerminalFiberBanks
public import Unfoldings.Roof.CompatibleTerminalBankIntervals

/-! Finite original comparison copies and continuous banks match the actual whole terminal banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance compatibleMeshTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


variable (W : R.WholeCutModel M)

local instance compatibleMeshTerminalWholeFintype : Fintype W.Index := W.finiteIndex

/-- Each specified original finite copy over a positive terminal point belongs to exactly
one named original whole bank, with equality of actual cut copies. -/
theorem existsUnique_compatibleMesh_terminalBank_side
    (r : {v // v ∈ R.parents.roots}) (t : ℝ≥0) (tpos : 0 < t.val)
    (y : (T).pairedComplex.Realization (Fcut).retain)
    (position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain y) =
      R.exterior.ray (R.terminalIndex r) t.val) :
    ∃! side : Bool,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W y =
          K.wholeTerminalBank compact nonempty R no_boundary W r side t := by
  apply K.existsUnique_wholeTerminalBank_side compact nonempty R no_boundary W r t tpos
  exact (congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W y)).trans position

/-- Every continuous connected finite comparison bank follows a single original whole
terminal bank, even across fine mesh vertices and at its finite truncation endpoint. -/
theorem compatibleMesh_terminalBank_side_constant
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (r : {v // v ∈ R.parents.roots})
    (curve : A → (T).pairedComplex.Realization (Fcut).retain) (continuous : Continuous curve)
    (time : A → ℝ≥0) (tpos : ∀ a, 0 < (time a).val)
    (position : ∀ a, Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain (curve a)) =
      R.exterior.ray (R.terminalIndex r) (time a).val) :
    ∃ side : Bool, ∀ a,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W (curve a) =
          K.wholeTerminalBank compact nonempty R no_boundary W r side (time a) := by
  apply K.wholeTerminalBank_side_constant compact nonempty R no_boundary W r
    (fun a => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W (curve a))
    ((K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W).continuous.comp continuous) time tpos
  intro a
  exact (congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W (curve a))).trans (position a)

/-- An original finite terminal bank is the restriction of one actual whole bank on a
closed interval, preserving the original source copy and the finite truncation endpoint. -/
theorem compatibleMesh_terminalBank_eq_on_Icc (r : {v // v ∈ R.parents.roots})
    {τ : ℝ} (tpos : 0 < τ)
    (curve : Set.Icc (0 : ℝ) τ → (T).pairedComplex.Realization (Fcut).retain)
    (continuous : Continuous curve)
    (position : ∀ t, Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain (curve t)) =
      R.exterior.ray (R.terminalIndex r) t.val) :
    ∃ side : Bool, ∀ t,
      K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W (curve t) =
          K.wholeTerminalBank compact nonempty R no_boundary W r side ⟨t.val, t.property.1⟩ := by
  apply K.wholeTerminalBank_eq_on_Icc compact nonempty R no_boundary W r tpos
    (fun t => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W (curve t))
    ((K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W).continuous.comp continuous)
  intro t
  exact (congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W (curve t))).trans (position t)

end Unfoldings.ConvexRoof
