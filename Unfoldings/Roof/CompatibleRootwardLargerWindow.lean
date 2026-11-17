module

public import Unfoldings.Roof.CompatibleComparisonWholeEnvelope
public import Unfoldings.Roof.CompatibleRootwardWindowCompletion

/-! Larger support-capturing roofs construct actual respected short-window comparisons. -/

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

local instance rootwardLargerWindowChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardLargerWindowChartWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "ImageAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[j]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side j h k hk)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

open Classical in
local instance rootwardLargerWindowNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "StemAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

local notation "NewConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewHigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "NewRoofAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
  NewConformingAt[S,L,h]
  (K.compatible_section_interior compact nonempty R L NewHigherAt[L,h] M)

local notation "ContinuedAt[" j "," h "," k "," hk "," t "]" =>
  K.compatibleMeshContinuedRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk t
local notation "WindowAt[" j "," h "," k "," hk "," t "," f "," n "," hf "]" =>
  PolygonalChain.interval (K.compatibleMeshContinuedRootwardPath compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side j h k hk t) f (n + 2) hf
local notation "Equations" => K.compatibleCutEquations compact nonempty R no_boundary level higher

open Classical in
local instance rootwardLargerWindowCompletionFintype
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    {φ : ℝ} {region : Set Plane} {J : Type} {extra : J → Plane →ᵃ[ℝ] ℝ}
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

open Classical in
/-- Every actual short rootward window constructs a larger support-capturing roof
and a respected physical comparison cap. One tilt works for all terminal durations;
the cap keeps the original whole graph throughout the Jordan comparison region. -/
theorem exists_uniform_compatibleRootwardWindow_larger_comparison {η : ℝ} (error_positive : 0 < η) :
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
        ∃ later : ℝ, ∃ ordered : level < later,
          (∀ c, (interior (W.partition.footprint c) ∩
            interior (SpatialEnvelope.clip M.plane (-later))).Nonempty) ∧
          R.terminalTime level RootAt[SourceAt[i],by omega] + time <
            R.terminalTime later RootAt[SourceAt[i],by omega] ∧
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
              ∃ E : (NewRoofAt[FrontierAt[i],later,ordered]).CompletionMesh φ
                  (PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c))
                  ((NewRoofAt[FrontierAt[i],later,ordered]).combinedCompletionEquations
                    (Sum.elim Equations (P.markedClosureEquations q c))),
                (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c),
                  SpatialEnvelope.height
                    ((NewRoofAt[FrontierAt[i],later,ordered]).completionPlanes
                      E.tentHeight (Real.sin φ / 2)) p =
                    SpatialEnvelope.height M.plane p) ∧
                E.cap.HasSmallRadialBankRolling P q c jordan η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_supported_window_rolling.{0, 0, 0} error_positive
  refine ⟨φ, bounds, ?_⟩
  intro normal i fresh m length time forward first n fits window_small δ room
  let root := RootAt[SourceAt[i],by omega]
  let final_time := R.terminalTime level root + time
  obtain ⟨later, large, captures⟩ := SpatialEnvelope.exists_level_capturing_support_cells
    W.partition (max level ((K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex root) final_time)))
  have ordered : level < later := (le_max_left _ _).trans_lt large
  have captured := captures later le_rfl
  have tail_before : final_time < R.terminalTime later root :=
    (R.terminal_ray_below_iff later (fun v => (higher v).trans ordered) root
      (add_nonneg (R.terminalTime_pos level higher root).le forward.le)).mp
      ((le_max_right _ _).trans_lt large)
  have tilt : (NewRoofAt[FrontierAt[i],later,ordered]).TiltBound φ :=
    fun f => normal ((NewAt[FrontierAt[i],later,ordered]).support f)
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
    uniform (NewRoofAt[FrontierAt[i],later,ordered]) tilt
      (WindowAt[i,fresh,m,length,time,first,n,fits])
      ((Q).projectedVertex SourceAt[i]) window_strict initial
      (K.compatibleMeshContinuedRootwardPath_edge_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W r side i fresh m length forward
        ⟨first + (n + 1), by omega⟩)
      genuine window_small (Q).projectedVertex Equations
      (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher) room
  refine ⟨later, ordered, captured, tail_before, s, t, first_trim, last_trim, q, c, height,
    nearby, radial, trimmed_initial, progress, supported, outside, outward, regular, vertices,
    first_link, middle_link, last_link, jordan, E, ?_, rolling⟩
  intro p member
  exact (preserved p member).trans
    (K.compatibleMeshProcessedComparisonRoofHeight_eq_whole compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered captured p)

end Unfoldings.ConvexRoof
