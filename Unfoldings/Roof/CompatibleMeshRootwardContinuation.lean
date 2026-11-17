module

public import Unfoldings.Roof.CompatibleMeshRootwardTerminal
public import Unfoldings.Roof.CompatibleMeshTerminalContinuation
public import Unfoldings.Geometry.ChainAppendInterval

/-! Continue actual rootward banks along their original terminal rays with radial margins. -/

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

local instance rootwardContinuationIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardContinuationWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Keep the actual original rootward bank and append a finite portion of its derived
terminal ray. No upper bound is imposed on the duration. -/
def compatibleMeshContinuedRootwardPath
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ) :
    PolygonalChain Plane (m + 2) :=
  (PathAt[i,fresh,m,length]).snoc
    (R.exterior.ray (R.terminalIndex RootAt[SourceAt[i],by omega])
      (R.terminalTime level RootAt[SourceAt[i],by omega] + time))

local notation "ContinuedAt[" j "," h "," k "," hk "," t "]" =>
  K.compatibleMeshContinuedRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk t
local notation "FullAt[" j "," k "," hk "," t "]" =>
  K.compatibleMeshContinuedHistory compact nonempty R no_boundary level higher M positive
    inner_disk beta acute SourceAt[j] (k + 2) (by omega) hk t

/-- Original rootward bank vertices, including the original truncation endpoint, do not move. -/
theorem compatibleMeshContinuedRootwardPath_vertex_castSucc
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ)
    (j : Fin (m + 2)) :
    (ContinuedAt[i,fresh,m,length,time]).vertex j.castSucc =
      (PathAt[i,fresh,m,length]).vertex j := PolygonalChain.snoc_vertex_castSucc _ _ _

/-- Continuation retains every actual point on every original directed bank. -/
theorem compatibleMeshContinuedRootwardPath_point_castSucc
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ)
    (j : Fin (m + 1)) (t : unitInterval) :
    (ContinuedAt[i,fresh,m,length,time]).point j.castSucc t =
      (PathAt[i,fresh,m,length]).point j t := PolygonalChain.snoc_point_castSucc _ _ _ _

/-- The appended link has exactly the original terminal direction and prescribed duration. -/
theorem compatibleMeshContinuedRootwardPath_edge_last
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ) :
    (ContinuedAt[i,fresh,m,length,time]).edge (Fin.last (m + 1)) =
      time • R.exterior.direction (R.exterior.slope (R.terminalIndex
        RootAt[SourceAt[i],by omega])) := by
  rw [compatibleMeshContinuedRootwardPath, PolygonalChain.snoc_edge_last,
    K.compatibleMeshCurrentRootwardPath_last_terminalPoint]
  change R.exterior.ray _ (_ + time) - R.exterior.ray _ _ = _
  simp only [SlopeEnvelope.ExteriorPlan.ray]
  module

/-- The appended bank is an exact terminal interval of the full original continued history. -/
theorem compatibleMeshContinuedRootwardPath_eq_history
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ) :
    ContinuedAt[i,fresh,m,length,time] = (FullAt[i,m,length,time]).interval 1 (m + 2)
      (by omega) := by
  change (PathAt[i,fresh,m,length]).snoc _ =
    ((HistoryAt[i,m]).snoc _).interval 1 (m + 2) _
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  exact (HistoryAt[i,m]).interval_snoc 1 (m + 1) (by omega) _

/-- The appended actual stem still follows the original routing at every fine bank. -/
theorem compatibleMeshContinuedRootwardPath_follows
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) : R.Follows ContinuedAt[i,fresh,m,length,time] := by
  rw [K.compatibleMeshContinuedRootwardPath_eq_history]
  exact R.follows_interval FullAt[i,m,length,time]
    (K.compatibleMeshContinuedHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute SourceAt[i] (m + 2) (by omega) length forward) 1 (m + 2) (by omega)

/-- The original whole-stem length estimate includes arbitrarily long appended terminal banks. -/
theorem compatibleMeshContinuedRootwardPath_length_bound
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) {b : ℝ} (upper : ∀ p ∈ slopes, ‖p‖ ≤ b) :
    (ContinuedAt[i,fresh,m,length,time]).projectedLength ≤ (b / (a * Real.cos β)) *
      ‖(ContinuedAt[i,fresh,m,length,time]).vertex (Fin.last (m + 2)) -
        (ContinuedAt[i,fresh,m,length,time]).vertex 0‖ :=
  R.follows_length_bound positive beta acute inner_disk upper ContinuedAt[i,fresh,m,length,time]
    (K.compatibleMeshContinuedRootwardPath_follows compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length forward)

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- The actual fresh source controls the entire original bank and every finite terminal tail. -/
theorem compatibleMeshContinuedRootwardPath_source_margin
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) (j : Fin (m + 2)) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖(ContinuedAt[i,fresh,m,length,time]).vertex j.castSucc -
          (Q).projectedVertex SourceAt[i]‖ * ‖(ContinuedAt[i,fresh,m,length,time]).edge j‖) ≤
      inner ℝ ((ContinuedAt[i,fresh,m,length,time]).vertex j.castSucc -
        (Q).projectedVertex SourceAt[i]) ((ContinuedAt[i,fresh,m,length,time]).edge j) := by
  have margin := R.follows_subhistory_radial_margin FullAt[i,m,length,time]
    (K.compatibleMeshContinuedHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk beta acute SourceAt[i] (m + 2) (by omega) length forward)
    positive beta acute bpos ratio inner_disk upper small 0 ⟨1 + j.val, by omega⟩ (Nat.zero_le _)
  rw [K.compatibleMeshContinuedRootwardPath_eq_history]
  rwa [K.compatibleMeshContinuedHistory_vertex_zero] at margin

/-- Distance from the actual fresh source increases throughout the whole continued stem. -/
theorem compatibleMeshContinuedRootwardPath_radialFrom_source
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) :
    (ContinuedAt[i,fresh,m,length,time]).RadialFrom ((Q).projectedVertex SourceAt[i]) 0 := by
  intro j _
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  have margin := K.compatibleMeshContinuedRootwardPath_source_margin compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length
    forward j
  exact (mul_nonneg (fine_annular_radial_margin_pos small).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans margin

/-- The actual fresh source remains a strict radial source for every finite terminal duration. -/
theorem compatibleMeshContinuedRootwardPath_strictRadialSource
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) :
    (Q).projectedVertex SourceAt[i] ∈ (ContinuedAt[i,fresh,m,length,time]).strictRadialSources := by
  apply (ContinuedAt[i,fresh,m,length,time]).strictRadialSource_of_margin
    (fine_annular_radial_margin_pos small)
    (K.compatibleMeshContinuedRootwardPath_radialFrom_source compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length
      forward)
  · have initial := K.compatibleMeshCurrentRootwardPath_initial_dist_pos compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
    change 0 < dist ((Q).projectedVertex SourceAt[i])
      ((ContinuedAt[i,fresh,m,length,time]).vertex (0 : Fin (m + 2)).castSucc)
    rwa [K.compatibleMeshContinuedRootwardPath_vertex_castSucc]
  · exact K.compatibleMeshContinuedRootwardPath_source_margin compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length
      forward

/-- Whole-point radial order from every earlier point persists along the continued actual stem. -/
theorem compatibleMeshContinuedRootwardPath_globallyRadiallyMonotone
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) :
    (ContinuedAt[i,fresh,m,length,time]).GloballyRadiallyMonotone :=
  R.follows_globallyRadiallyMonotone ContinuedAt[i,fresh,m,length,time]
    (K.compatibleMeshContinuedRootwardPath_follows compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length forward)
    positive beta acute bpos ratio inner_disk upper small

end Unfoldings.ConvexRoof
