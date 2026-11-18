module

public import Unfoldings.Roof.SupportedOriginalBankWindow
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Roof.CompatibleProcessedCutBankInterior
public import Unfoldings.Roof.CompatibleMeshRootwardGeometry
public import Unfoldings.Polyhedron.ProjectedBoundaryChainInterval

/-! Actual short rootward bank windows construct respected physical real-heading comparisons. -/

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

local instance actualRootwardWindowIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance actualRootwardWindowWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "MapAt[" j "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W FrontierAt[j]
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

local instance actualRootwardWindowCompletionFintype {FineFace : Type} [Fintype FineFace]
    {D : TriangleComplex.{0, 0} FineFace} {L : ConvexRoof D} {φ : ℝ} {region : Set Plane}
    {J : Type} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : L.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Every actual short current-rootward bank interval constructs a respected physical
comparison and a uniformly small original real terminal-heading error. Its cuts,
trims, perturbed source, supported Jordan closure and entire physical bank window
are constructed from the actual compatible forest; no matching certificate is assumed. -/
theorem exists_uniform_compatibleRootward_actual_window {η : ℝ} (error_positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∀ f, Real.cos φ ≤ (M.plane f).normal 2) →
      ∀ (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
        (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
        (first n : ℕ) (fits : first + (n + 1) ≤ m),
        let actual := (ChainAt[i,fresh,m,length]).interval first (n + 1) fits
        let P := (Q).folding.projectedBoundaryChain actual
        (∑ k : Fin n, InnerProductGeometry.angle
          (P.internalSourceRay ((Q).projectedVertex SourceAt[i]) k.castSucc)
          (P.internalSourceRay ((Q).projectedVertex SourceAt[i]) k.succ)) < Real.pi / 4 →
        ∀ {δ : ℝ}, 0 < δ →
          ∃ cut : ∀ j, ¬ (T).pairedComplex.IsBoundaryEdge Set.univ
              ((T).pairedComplex.germEdge (actual.point j).val),
          ∃ (s t : unitInterval) (start : 0 < s.val ∧ s.val < 1)
            (finish : 0 < t.val ∧ t.val < 1), ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
            let trimmed := P.trimEnds s t
            dist q ((Q).projectedVertex SourceAt[i]) < δ ∧ trimmed.RadialFrom q 0 ∧
            0 < dist q (trimmed.vertex 0) ∧
            (∀ z ∈ Set.range trimmed.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
            0 < inner ℝ (trimmed.vertex (Fin.last (n + 2)) - q)
              (c - trimmed.vertex (Fin.last (n + 2))) ∧
            ∃ jordan : Schoenflies.IsJordanCurve (trimmed.threeSegmentClosure q c),
              ∃ E : (Q).CompletionMesh φ
                  (PlanarTopology.closedJordanDomain (trimmed.threeSegmentClosure q c))
                  ((Q).combinedCompletionEquations (trimmed.markedClosureEquations q c)),
                (∀ p ∈ PlanarTopology.closedJordanDomain (trimmed.threeSegmentClosure q c),
                  SpatialEnvelope.height ((Q).completionPlanes E.tentHeight
                    (Real.sin φ / 2)) p = (Q).roofHeight p) ∧
                let window := CompletionMesh.markedOriginalBankWindow actual cut s t q c
                  start.2 finish.2 jordan E
                |(T).pairedComplex.boundaryChainRollHeading actual (Fin.last (n + 1)) -
                  E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
                    window.chain (Fin.last window.length)| < η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_supported_original_bank_window.{0, 0} error_positive
  refine ⟨φ, bounds, ?_⟩
  intro normal i fresh m length first n fits
  dsimp only
  intro short δ room
  let actual := (ChainAt[i,fresh,m,length]).interval first (n + 1) fits
  let P := (Q).folding.projectedBoundaryChain actual
  let origin := (Q).projectedVertex SourceAt[i]
  have cut (j : Fin (n + 2)) : ¬ (T).pairedComplex.IsBoundaryEdge Set.univ
      ((T).pairedComplex.germEdge (actual.point j).val) := by
    let old := (ChainAt[i,fresh,m,length]).intervalIndex first (n + 1) fits j
    exact K.compatibleMeshProcessed_boundaryEnd_is_cut_of_height_lt compact nonempty R no_boundary
      level higher M positive inner_disk beta acute FrontierAt[i]
      ((ChainAt[i,fresh,m,length]).point old)
      (K.compatibleMeshCurrentRootwardChain_corner_height_lt compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W r side i fresh m length old)
  have base_geometry : (Q).folding.projectedBoundaryChain (ChainAt[i,fresh,m,length]) =
      PathAt[i,fresh,m,length] := rfl
  have geometry : P = (PathAt[i,fresh,m,length]).interval first (n + 2) (by omega) :=
    ((Q).folding.projectedBoundaryChain_interval (ChainAt[i,fresh,m,length]) first (n + 1)
      fits).trans (congrArg (fun A : PolygonalChain Plane (m + 1) =>
        A.interval first (n + 2) (by omega)) base_geometry)
  have strict := K.compatibleMeshCurrentRootwardPath_strictRadialSource compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length
  have strict_interval : origin ∈
      ((PathAt[i,fresh,m,length]).interval first (n + 2) (by omega)).strictRadialSources := by
    intro j nonzero
    exact strict ⟨first + j.val, by have bound := j.isLt; omega⟩ nonzero
  have strict_P : origin ∈ P.strictRadialSources := Eq.mpr
    (congrArg (fun A : PolygonalChain Plane (n + 2) => origin ∈ A.strictRadialSources) geometry)
    strict_interval
  have initial := K.compatibleMeshCurrentRootwardPath_initial_dist_pos compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  have radial := K.compatibleMeshCurrentRootwardPath_radialFrom_source compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length
  have lower := radial.dist_vertices_le (PathAt[i,fresh,m,length]) 0
    ⟨first, by omega⟩ le_rfl (Fin.zero_le _)
  have initial_interval : 0 < dist origin
      (((PathAt[i,fresh,m,length]).interval first (n + 2) (by omega)).vertex 0) :=
    initial.trans_le lower
  have initial_P : 0 < dist origin (P.vertex 0) := Eq.mpr
    (congrArg (fun A : PolygonalChain Plane (n + 2) => 0 < dist origin (A.vertex 0)) geometry)
    initial_interval
  have tilt : (Q).TiltBound φ := fun f => normal ((T).support f)
  obtain ⟨s, t, start, finish, q, c, height, nearby, trimmed_radial, trimmed_initial,
      supported, excluded, outward, jordan, E, preserved, estimate⟩ :=
    uniform (Q) tilt RetainAt[FrontierAt[i]] actual cut origin strict_P initial_P short room
  exact ⟨cut, s, t, start, finish, q, c, height, nearby, trimmed_radial, trimmed_initial,
    supported, excluded, outward, jordan, E, preserved, estimate⟩

end Unfoldings.ConvexRoof
