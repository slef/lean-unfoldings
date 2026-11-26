module

public import Unfoldings.FewestNets.ThreeExitGraftTerminalCoverage
public import Unfoldings.Cone.TransportedCharts
public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! The exact tangent sectors of finite roof corners in the whole cut. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance wholeCutVertexIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Base" => contourBaseMark L S
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "retain" => PotentialCutForest.retain Fcut
local notation "intoCut" => L.fineMeshWholeMap S.higher
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "Forget[" w "]" => TriangleComplex.vertexForgetCuts D (Set.subset_univ retain) w
local notation "CutPoint[" w "]" => intoCut (TriangleComplex.vertexPoint D retain w)

/-- A cut copy of an original nonroot vertex lies strictly inside the window. -/
theorem contourCutVertex_below (w : (D).Vertex retain)
    (nonroot : Forget[w] ∉ (Fcut).parents.roots) :
    (G).height (Cap.horizontal (restore CutPoint[w]).val) < level := by
  rw [L.restore_fineMeshWholeMap]
  have position : (T).pairedFolding.toSpace retain ((D).vertexPoint retain w) =
      (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ Forget[w]) := by
    rw [(D).vertexPoint_vertexForgetCuts, (T).pairedFolding.toSpace_forgetCuts]
  rw [position]
  exact contourParentStart_below S ⟨Forget[w], nonroot⟩

/-- The local inclusion of a specified finite point fills a whole ball of the physical cut. -/
theorem exists_fineMesh_ball_chart_at (y : (D).Realization retain)
    (below : (G).height (Cap.horizontal (restore (intoCut y)).val) < level) :
    ∃ r > 0, ∃ chart : Metric.eball y (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (intoCut y) (ENNReal.ofReal r),
      ∀ z, (chart z).val = intoCut z.val := by
  obtain ⟨x, same, r, positive, chart, values⟩ :=
    L.exists_fineMesh_ball_chart S.higher (intoCut y) below
  have eq := L.fineMeshWholeMap_injective_at S.higher y x below same.symm
  subst x
  exact ⟨r, positive, chart, values⟩

/-- The exact retained finite tangent fan persists at the vertex copy of the whole cut. -/
theorem contourCutVertex_tangent_chart (w : (D).Vertex retain)
    (nonroot : Forget[w] ∉ (Fcut).parents.roots) :
    ∃ r > 0, ∃ chart : Metric.eball ((D).tangentOrigin retain w) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball CutPoint[w] (ENNReal.ofReal r),
      ∀ (a : (D).TangentTotal retain w)
        (near : edist ((D).tangentPoint retain w a) ((D).tangentOrigin retain w) < ENNReal.ofReal r),
        (chart ⟨(D).tangentPoint retain w a, near⟩).val =
          intoCut ((D).tangentSurfaceTag retain w a) :=
  (T).pairedFolding.exists_tangentChart_of_localMap retain w intoCut
    (L.exists_fineMesh_ball_chart_at S _ (L.contourCutVertex_below S w nonroot))

/-- An ordered boundary germ orients the whole physical roof sector, with exact
parameters on its two incident banks. -/
theorem contourCutVertex_directed_chart (b : (D).BoundaryEnd retain)
    (nonroot : Forget[(D).boundaryEndVertex retain b] ∉ (Fcut).parents.roots)
    (small : (D).totalAngle retain ((D).boundaryEndVertex retain b) < 2 * Real.pi) :
    let w := (D).boundaryEndVertex retain b
    let c := (D).boundaryMate retain b
    let θ := (D).totalAngle retain w
    ∃ r > 0, ∃ chart : Metric.eball CutPoint[w] (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin ((D).totalAngle_pos retain w).le) (ENNReal.ofReal r),
      (∀ (t : unitInterval)
        (near : edist (intoCut ((D).directedBoundaryPath b t)) CutPoint[w] < ENNReal.ofReal r),
        (chart ⟨intoCut ((D).directedBoundaryPath b t), near⟩).val.val =
          (t.val * (D).boundaryBankLength b : ℝ)) ∧
      (∀ (t : unitInterval)
        (near : edist (intoCut ((D).directedBoundaryPath c t)) CutPoint[w] < ENNReal.ofReal r),
        (chart ⟨intoCut ((D).directedBoundaryPath c t), near⟩).val.val =
          (t.val * (D).boundaryBankLength c) • polarRay θ) := by
  let w := (D).boundaryEndVertex retain b
  apply (D).exists_directedIntervalChart retain b intoCut small _
    (L.contourCutVertex_tangent_chart S w nonroot)
  intro c vertex t
  have zero : (D).directedBoundaryPath c 0 = (D).vertexPoint retain w :=
    ((D).directedBoundaryPath_zero c).trans (congrArg ((D).vertexPoint retain) vertex)
  rw [← zero, L.fineMeshWholeMap_edist_bank, (T).pairedFolding.edist_directedBoundaryPath_eq_length]
  rw [mul_comm t.val, ENNReal.ofReal_mul ((D).boundaryBankLength_pos c).le, edist_dist]
  congr 1
  apply congrArg ENNReal.ofReal
  change t.val = dist t.val 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
