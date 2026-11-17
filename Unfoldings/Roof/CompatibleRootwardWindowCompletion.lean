module

public import Unfoldings.Roof.CompatibleMeshRootwardTerminal
public import Unfoldings.Roof.CompatibleMeshTerminalContinuation
public import Unfoldings.Roof.CompatibleMeshRootwardContinuation
public import Unfoldings.Roof.CompatibleMeshWholeEnvelope
public import Unfoldings.Roof.SupportedWindowRolling

/-! Actual continued rootward windows construct physical whole-roof comparisons. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

local instance rootwardComparisonCompletionFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

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

local instance rootwardComparisonIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "ContinuedAt[" j "," h "," k "," hk "," t "]" =>
  K.compatibleMeshContinuedRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk t
local notation "WindowAt[" j "," h "," k "," hk "," t "," f "," n "," hf "]" =>
  PolygonalChain.interval (K.compatibleMeshContinuedRootwardPath compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side j h k hk t) f (n + 2) hf
local notation "Equations" => K.compatibleCutEquations compact nonempty R no_boundary level higher
/-- Every edge of a positive original terminal continuation is genuine, including the join. -/
theorem compatibleMeshContinuedRootwardPath_edge_ne_zero
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 < time) (j : Fin (m + 2)) :
    (ContinuedAt[i,fresh,m,length,time]).edge j ≠ 0 := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [K.compatibleMeshContinuedRootwardPath_edge_last]
    apply smul_ne_zero forward.ne'
    intro zero
    have unit := R.exterior.unit (R.terminalIndex RootAt[SourceAt[i],by omega])
    rw [zero, norm_zero] at unit
    norm_num at unit
  · change ((PathAt[i,fresh,m,length]).snoc _).edge k.castSucc ≠ 0
    rw [PolygonalChain.snoc_edge_castSucc]
    exact K.compatibleMeshCurrentRootwardPath_edge_ne_zero compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length k

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- Every original vertex, including arbitrary terminal extensions, stays away from the fresh
source. This supplies genuine source rays on windows crossing the truncation junction. -/
theorem compatibleMeshContinuedRootwardPath_vertex_dist_pos
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    {time : ℝ} (forward : 0 ≤ time) (j : Fin (m + 3)) :
    0 < dist ((Q).projectedVertex SourceAt[i])
      ((ContinuedAt[i,fresh,m,length,time]).vertex j) := by
  have radial := K.compatibleMeshContinuedRootwardPath_radialFrom_source compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length forward
  have initial : 0 < dist ((Q).projectedVertex SourceAt[i])
      ((ContinuedAt[i,fresh,m,length,time]).vertex 0) := by
    change 0 < dist ((Q).projectedVertex SourceAt[i])
      ((ContinuedAt[i,fresh,m,length,time]).vertex (0 : Fin (m + 2)).castSucc)
    rw [K.compatibleMeshContinuedRootwardPath_vertex_castSucc]
    exact K.compatibleMeshCurrentRootwardPath_initial_dist_pos compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length
  exact initial.trans_le ((ContinuedAt[i,fresh,m,length,time]).path_radius_bounds
    ((Q).projectedVertex SourceAt[i]) radial
    ((ContinuedAt[i,fresh,m,length,time]).vertex_mem_path_range j)).1

variable (captured : ∀ c, (interior (W.partition.footprint c) ∩
  interior (SpatialEnvelope.clip M.plane (-level))).Nonempty)

include captured

open Classical in
/-- Actual short windows, including arbitrary terminal durations and the original junction,
construct regular physical comparison caps. The full original roof is preserved even outside
the finite clip; one tilt controls every window independently of the chosen duration. -/
theorem exists_uniform_compatibleRootwardWindow_comparison {η : ℝ} (error_positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∀ f, Real.cos φ ≤ (M.plane f).normal 2) →
      ∀ (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
        (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
        (time : ℝ), 0 < time → ∀ (first n : ℕ) (fits : first + (n + 2) ≤ m + 2),
        (∑ k : Fin n, InnerProductGeometry.angle
          ((WindowAt[i,fresh,m,length,time,first,n,fits]).internalSourceRay
            ((Q).projectedVertex SourceAt[i]) k.castSucc)
          ((WindowAt[i,fresh,m,length,time,first,n,fits]).internalSourceRay
            ((Q).projectedVertex SourceAt[i]) k.succ)) < Real.pi / 4 →
        ∀ {δ : ℝ}, 0 < δ →
        ∃ s t : unitInterval, (0 < s.val ∧ s.val < 1) ∧ (0 < t.val ∧ t.val < 1) ∧
          ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
            let P := (WindowAt[i,fresh,m,length,time,first,n,fits]).trimEnds s t
            dist q ((Q).projectedVertex SourceAt[i]) < δ ∧ P.RadialFrom q 0 ∧
            0 < dist q (P.vertex 0) ∧ dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 2))) ∧
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
            0 < inner ℝ (P.vertex (Fin.last (n + 2)) - q) (c - P.vertex (Fin.last (n + 2))) ∧
            (∀ j, Equations j q ≠ 0 ∧ Equations j c ≠ 0) ∧
            (∀ v, q ≠ (Q).projectedVertex v ∧ c ≠ (Q).projectedVertex v) ∧
            (∀ v, (Q).projectedVertex v ∈ segment ℝ (P.vertex 0) q →
              (Q).projectedVertex v = P.vertex 0) ∧
            (∀ v, (Q).projectedVertex v ∉ segment ℝ q c) ∧
            (∀ v, (Q).projectedVertex v ∈ segment ℝ (P.vertex (Fin.last (n + 2))) c →
              (Q).projectedVertex v = P.vertex (Fin.last (n + 2))) ∧
            ∃ jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c),
              ∃ E : (Q).CompletionMesh φ
                  (PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c))
                  ((Q).combinedCompletionEquations
                    (Sum.elim Equations (P.markedClosureEquations q c))),
                (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c),
                  SpatialEnvelope.height
                    ((Q).completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                    SpatialEnvelope.height M.plane p) ∧
                E.cap.HasSmallRadialBankRolling P q c jordan η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_supported_window_rolling.{0, 0, 0} error_positive
  refine ⟨φ, bounds, ?_⟩
  intro normal i fresh m length time forward first n fits window_small δ room
  have tilt : (Q).TiltBound φ := fun f => normal ((T).support f)
  have strict := K.compatibleMeshContinuedRootwardPath_strictRadialSource compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length forward.le
  have window_strict : (Q).projectedVertex SourceAt[i] ∈
      (WindowAt[i,fresh,m,length,time,first,n,fits]).strictRadialSources := by
    intro k nonzero
    exact strict ⟨first + k.val, by omega⟩ nonzero
  have distances := K.compatibleMeshContinuedRootwardPath_vertex_dist_pos compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length forward.le
  have initial : 0 < dist ((Q).projectedVertex SourceAt[i])
      ((WindowAt[i,fresh,m,length,time,first,n,fits]).vertex 0) := distances ⟨first, by omega⟩
  have genuine (k : Fin (n + 1)) :
      (WindowAt[i,fresh,m,length,time,first,n,fits]).internalSourceRay
        ((Q).projectedVertex SourceAt[i]) k ≠ 0 := by
    intro zero
    have same := sub_eq_zero.mp zero
    exact (dist_pos.mp (distances ⟨first + (k.val + 1), by omega⟩)) same.symm
  obtain ⟨s, t, first_trim, last_trim, q, c, height, nearby, radial, trimmed_initial,
      progress, supported, outside, outward, regular, vertices, first_link, middle_link,
      last_link, jordan, E, preserved, rolling⟩ :=
    uniform (Q) tilt (WindowAt[i,fresh,m,length,time,first,n,fits])
      ((Q).projectedVertex SourceAt[i]) window_strict initial
      (K.compatibleMeshContinuedRootwardPath_edge_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W r side i fresh m length forward
        ⟨first + (n + 1), by omega⟩)
      genuine window_small (Q).projectedVertex Equations
      (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher) room
  refine ⟨s, t, first_trim, last_trim, q, c, height, nearby, radial, trimmed_initial,
    progress, supported, outside, outward, regular, vertices, first_link, middle_link,
    last_link, jordan, E, ?_, rolling⟩
  intro p member
  exact (preserved p member).trans (K.compatibleMeshRoofHeight_eq_whole compact nonempty R
    no_boundary M positive inner_disk W level higher captured p)

end Unfoldings.ConvexRoof

