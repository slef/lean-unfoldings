module

public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.RestoredWholeTerminalBanks

/-! Actual restored terminal banks remain separated beyond the original finite window. -/

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

local instance processedTerminalIndexFintype : Fintype (T).Index :=
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

local instance processedTerminalWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Every actual finite current copy lies strictly before the positive outer terminal tail
in the intrinsic whole cut. No planar development or injectivity assumption is needed. -/
theorem compatibleMeshProcessedWholeMap_ne_outer_terminalBank
    (S : (Fcut).parents.ParentFrontier) (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) (after : R.terminalTime level r < t.val)
    (y : (T).pairedComplex.Realization RetainAt[S]) :
    K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S y ≠
    K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side t
      := by
  intro same
  have in_clip : Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] y) ∈
      SpatialEnvelope.clip M.plane (-level) :=
    (T).toTriangulation.pairedFolding_footprint.subset
      ⟨_, ((T).pairedFolding.range_toSpace _).subset ⟨y, rfl⟩, rfl⟩
  rw [M.clip_eq_sublevel, neg_neg] at in_clip
  have mapped := K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S y
  have physical := mapped.symm.trans
    ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val) same).trans
      (K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
        r side t))
  have position := (congrArg Cap.horizontal physical).trans (SpatialEnvelope.horizontal_point _ _)
  have below := Eq.mp (congrArg (fun p =>
    (K.clippedExtension slopes compact nonempty).height p ≤ level) position) in_clip
  exact (not_lt_of_ge ((R.terminal_ray_sublevel_iff level higher r t.property).mp below)) after

/-- Outside the finite window, the intermediate cut has the exact original whole-cut germ. -/
theorem exists_compatibleMeshProcessed_cut_germ_outside (S : (Fcut).parents.ParentFrontier)
    {p : Plane} (above : level < (K.clippedExtension slopes compact nonempty).height p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z p < ε → (z ∈ R.carrier ↔ z ∈ CutsAt[S]) := by
  have opened : IsOpen {p | level < (K.clippedExtension slopes compact nonempty).height p} :=
    isOpen_lt continuous_const (K.clippedExtension slopes compact nonempty).continuous_height
  obtain ⟨ε, radius_positive, ball⟩ := Metric.isOpen_iff.mp opened p above
  exact ⟨ε, radius_positive, fun z near =>
    (K.mem_compatibleMeshProcessedCarrier_outside compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S (ball (Metric.mem_ball.mpr near)).le).symm⟩

/-- Opposite named original banks stay distinct past the truncation in every actual
intermediate whole cut, even if restoration merges their earlier endpoint copies. -/
theorem compatibleMeshProcessed_terminalBank_ne (S : (Fcut).parents.ParentFrontier)
    (r : {v // v ∈ R.parents.roots}) (side other : Bool) (different : side ≠ other)
    (s t : ℝ≥0) (after : R.terminalTime level r < s.val) :
    K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side s ≠
      K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r
        other t := by
  have above : level < (K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex r) s.val) := by
    apply lt_of_not_ge
    intro below
    exact (not_lt_of_ge ((R.terminal_ray_sublevel_iff level higher r s.property).mp below)) after
  obtain ⟨ε, radius_positive, same_germ⟩ := K.exists_compatibleMeshProcessed_cut_germ_outside
    compact nonempty
    R no_boundary level higher M positive inner_disk beta acute S above
  intro equal
  apply K.wholeTerminalBank_ne compact nonempty R no_boundary W r side other different s t
    ((R.terminalTime_pos level higher r).trans after)
  apply W.partition.forgetCut_injective_at_of_local_eq R.carrier CutsAt[S] IncludedAt[S]
    (K.wholeTerminalBank compact nonempty R no_boundary W r side s) radius_positive ?_
    (K.wholeTerminalBank compact nonempty R no_boundary W r other t) equal
  intro z near
  apply same_germ z
  have point := (congrArg Cap.horizontal
    (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side s)).trans
      (SpatialEnvelope.horizontal_point _ _)
  rwa [point] at near

end Unfoldings.ConvexRoof
