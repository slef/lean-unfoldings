module

public import Unfoldings.Roof.CompatibleRootwardTerminalJoin
public import Unfoldings.Roof.TerminalArrival
public import Unfoldings.Roof.TerminalJunctionGerm
public import Unfoldings.Roof.ProcessedParentSegments
public import Unfoldings.Geometry.SpatialEnvelopeCutBall

/-! Actual final rootward banks retain the original whole-cut germ at their terminal joins. -/

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

local instance rootwardJunctionGermIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardJunctionGermWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

local notation "SourceAt[" j "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "FrontierAt[" j "]" => TriangleComplex.contourFrontier
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)
local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "ChainAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

/-- The original last current parent segment is still cut, including its actual rim endpoint. -/
theorem compatibleMeshCurrentRootwardPath_last_segment_cut
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    segment ℝ ((PathAt[i,fresh,m,length]).vertex (Fin.last m).castSucc)
      ((PathAt[i,fresh,m,length]).vertex (Fin.last (m + 1))) ⊆ CutsAt[FrontierAt[i]] := by
  let vertex := (Fcut).parents.parent^[m + 1] SourceAt[i]
  have nonroot : vertex ∉ (Fcut).parents.roots :=
    (Fcut).parents.iterate_lt_distanceToRoot_not_mem SourceAt[i] (by rw [length]; omega)
  have single := K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh
  have processed : vertex ∈ (FrontierAt[i]).processed :=
    ((FrontierAt[i]).contactTime_le_iff SourceAt[i] (m + 1)).mp (by rw [single]; omega)
  have selected := (Fcut).processed_parent_segment_subset FrontierAt[i] vertex nonroot processed
  have position (j : Fin (m + 2)) : (PathAt[i,fresh,m,length]).vertex j =
      (Q).projectedVertex ((Fcut).parents.parent^[1 + j.val] SourceAt[i]) := by
    rw [K.compatibleMeshCurrentRootwardPath_eq_history]
    rfl
  have first : (PathAt[i,fresh,m,length]).vertex (Fin.last m).castSucc =
      (Q).projectedVertex vertex := by
    simpa only [Fin.val_castSucc, Fin.val_last, Nat.add_comm] using position (Fin.last m).castSucc
  have last : (PathAt[i,fresh,m,length]).vertex (Fin.last (m + 1)) =
      (Q).projectedVertex ((Fcut).parents.parent vertex) := by
    have equal : (Fcut).parents.parent vertex = (Fcut).parents.parent^[m + 2] SourceAt[i] :=
      (Function.iterate_succ_apply' (Fcut).parents.parent (m + 1) SourceAt[i]).symm
    exact (position _).trans (congrArg (Q).projectedVertex (by
      rw [equal]
      congr 1
      simp only [Fin.val_last]
      omega))
  rw [first, last]
  exact fun p member => Or.inr (selected member)

/-- The actual last original bank reaches the derived terminal point along that very ray,
strictly after an original nonnegative parameter. -/
theorem exists_compatibleMeshCurrentRootwardPath_terminal_arrival
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ s : ℝ, 0 ≤ s ∧ s < R.terminalTime level RootAt[SourceAt[i],by omega] ∧
      (PathAt[i,fresh,m,length]).vertex (Fin.last m).castSucc =
        R.exterior.ray (R.terminalIndex RootAt[SourceAt[i],by omega]) s := by
  have last := K.compatibleMeshCurrentRootwardPath_last_terminalPoint compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side i fresh m length
  have step := K.compatibleMeshCurrentRootwardPath_follows compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh m length (Fin.last m)
  rw [Fin.succ_last, last] at step
  apply K.followsStep_to_terminalPoint compact nonempty R no_boundary level higher
    RootAt[SourceAt[i],by omega] step
  intro same
  have nonzero := K.compatibleMeshCurrentRootwardPath_edge_ne_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side i fresh m length (Fin.last m)
  apply nonzero
  simp only [PolygonalChain.edge, Fin.succ_last, last, same, sub_self]

/-- The actual incoming current bank and fixed outer tail retain the exact original cut
near the terminal junction. This derives the cut germ from the constructed processing stage. -/
theorem exists_compatibleMeshCurrentRootwardEnd_cut_germ
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z,
      dist z (R.terminalPoint level RootAt[SourceAt[i],by omega]) < ε →
      (z ∈ R.carrier ↔ z ∈ CutsAt[FrontierAt[i]]) := by
  obtain ⟨s, nonnegative, before, first⟩ :=
    K.exists_compatibleMeshCurrentRootwardPath_terminal_arrival compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length
  have selected := K.compatibleMeshCurrentRootwardPath_last_segment_cut compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  rw [first, K.compatibleMeshCurrentRootwardPath_last_terminalPoint] at selected
  exact K.exists_terminal_junction_cut_germ compact nonempty R no_boundary level higher
    CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] (fun _ member => Or.inl member)
    RootAt[SourceAt[i],by omega] nonnegative before selected

/-- Restoring unprocessed cuts preserves a whole original intrinsic ball at either bank
of the actual rootward terminal junction, including the endpoint itself. -/
theorem exists_compatibleMeshCurrentRootwardEnd_restore_chart
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (tailSide : Bool) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B :
      Metric.eball (K.wholeTerminalBank compact nonempty R no_boundary W
        RootAt[SourceAt[i],by omega] tailSide
        ⟨R.terminalTime level RootAt[SourceAt[i],by omega],
          (R.terminalTime_pos level higher _).le⟩) (ENNReal.ofReal ε) ≃ᵢ
      Metric.eball (K.restoredWholeTerminalBank compact nonempty R no_boundary W
        CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide
        ⟨R.terminalTime level RootAt[SourceAt[i],by omega],
          (R.terminalTime_pos level higher _).le⟩) (ENNReal.ofReal ε),
      ∀ y, (B y).val = W.partition.forgetCut R.carrier CutsAt[FrontierAt[i]]
        IncludedAt[FrontierAt[i]] y.val := by
  obtain ⟨δ, radius_positive, germ⟩ := K.exists_compatibleMeshCurrentRootwardEnd_cut_germ compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  apply W.partition.exists_forgetCut_ball_chart_at R.carrier CutsAt[FrontierAt[i]]
    IncludedAt[FrontierAt[i]] _ radius_positive
  intro z near
  apply germ z
  have point := (congrArg Cap.horizontal
    (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W
      RootAt[SourceAt[i],by omega] tailSide
      ⟨R.terminalTime level RootAt[SourceAt[i],by omega], (R.terminalTime_pos level higher
        _).le⟩)).trans
    (SpatialEnvelope.horizontal_point _ _)
  rwa [point] at near

end Unfoldings.ConvexRoof
