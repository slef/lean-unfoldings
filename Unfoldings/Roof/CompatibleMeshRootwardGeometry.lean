module

public import Unfoldings.Roof.CompatibleMeshRootwardChain
public import Unfoldings.Roof.SpatialEnvelopeBoundaryChains
public import Unfoldings.Complex.SupportedRootwardGeometry
public import Unfoldings.Roof.CompatibleMeshHistoryGeometry
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Actual current rootward banks are exact compatible histories with whole-point radial bounds. -/

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

local instance compatibleRootwardGeometryIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance compatibleRootwardGeometryWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "CurrentAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)

/-- The actual physical rootward bank path, in original projected coordinates. -/
def compatibleMeshCurrentRootwardPath
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    PolygonalChain Plane (m + 1) :=
  SpatialEnvelope.Triangulation.projectedBoundaryChain
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation
      (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk))
    (K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length)

/-- Every original rootward bank vertex, including the final rim copy, is the exact
corresponding vertex of the compatible fine history after its first fresh edge. -/
theorem compatibleMeshCurrentRootwardPath_eq_history
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length =
        (HistoryAt[i,m]).interval 1 (m + 1) (by omega) := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have far := (T).pairedFolding.rootwardParentBankChain_far_original_of_boundary_roots
      (Fcut).selection (Fcut).boundary_roots contour
      (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) i
      (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side i fresh) m length (Fin.last m)
    have projected := ((T).toTriangulation.projectedBoundaryChain_vertex_succ
      CurrentAt[i,fresh,m,length] conforming inside
      (Fin.last m)).trans (congrArg (Q).projectedVertex far)
    simpa [Fin.succ_last, Fin.val_last, compatibleMeshCurrentRootwardPath,
      SpatialEnvelope.Triangulation.projectedBoundaryChain, PolygonalChain.affineMap,
      compatibleMeshHistory, PolygonalChain.interval, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using projected
  · have original := K.compatibleMeshCurrentRootwardChain_original compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length k
    have projected := ((T).toTriangulation.projectedBoundaryChain_vertex_castSucc
      CurrentAt[i,fresh,m,length] conforming
      inside k).trans (congrArg (Q).projectedVertex original)
    simpa only [compatibleMeshCurrentRootwardPath,
      SpatialEnvelope.Triangulation.projectedBoundaryChain, PolygonalChain.affineMap,
      compatibleMeshHistory, PolygonalChain.interval, Fin.val_castSucc, Nat.add_comm] using
        projected

local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

/-- The actual physical bank path follows the original compatible routing at every fine step. -/
theorem compatibleMeshCurrentRootwardPath_follows
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    R.Follows PathAt[i,fresh,m,length] := by
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  exact R.follows_interval HistoryAt[i,m]
    (K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M positive
      inner_disk
      beta acute SourceAt[i] (m + 2) length.ge) 1 (m + 1) (by omega)

/-- The actual entire physical stem keeps the original common-potential length bound. -/
theorem compatibleMeshCurrentRootwardPath_length_bound
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) {b : ℝ}
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b) :
    (PathAt[i,fresh,m,length]).projectedLength ≤ (b / (a * Real.cos β)) *
      ‖(PathAt[i,fresh,m,length]).vertex (Fin.last (m + 1)) - (PathAt[i,fresh,m,length]).vertex
        0‖ :=
  R.follows_length_bound positive beta acute inner_disk upper PathAt[i,fresh,m,length]
    (K.compatibleMeshCurrentRootwardPath_follows compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute W r side i fresh m length)

/-- The actual source is distinct from the stem's first original parent vertex. -/
theorem compatibleMeshCurrentRootwardPath_initial_dist_pos
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    0 < dist ((Q).projectedVertex SourceAt[i]) ((PathAt[i,fresh,m,length]).vertex 0) := by
  have injective := K.compatibleMeshHistory_vertex_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute SourceAt[i] (m + 2) length.ge
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  apply dist_pos.mpr
  intro same
  have indices := injective (show (HistoryAt[i,m]).vertex 0 =
      (HistoryAt[i,m]).vertex ⟨1, by omega⟩ from same)
  have values := congrArg Fin.val indices
  change 0 = 1 at values
  omega

/-- Every actual bank edge is genuine, including the final original rim bank. -/
theorem compatibleMeshCurrentRootwardPath_edge_ne_zero
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (k : Fin (m + 1)) :
    (PathAt[i,fresh,m,length]).edge k ≠ 0 := by
  have injective := K.compatibleMeshHistory_vertex_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute SourceAt[i] (m + 2) length.ge
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  intro zero
  have indices := injective (sub_eq_zero.mp zero)
  have values := congrArg Fin.val indices
  change 1 + (k.val + 1) = 1 + k.val at values
  omega

/-- No vertex of the surviving stem coincides with the actual fresh source. -/
theorem compatibleMeshCurrentRootwardPath_vertex_ne_source
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (j : Fin (m + 2)) :
    (PathAt[i,fresh,m,length]).vertex j - (Q).projectedVertex SourceAt[i] ≠ 0 := by
  have injective := K.compatibleMeshHistory_vertex_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute SourceAt[i] (m + 2) length.ge
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  intro zero
  have indices := injective (show (HistoryAt[i,m]).vertex ⟨1 + j.val, by omega⟩ =
      (HistoryAt[i,m]).vertex 0 from sub_eq_zero.mp zero)
  have values := congrArg Fin.val indices
  change 1 + j.val = 0 at values
  omega

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
  (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- Quantitative whole-path margins hold against the actual fresh source, which lies
before the stem's first parent bank. No coarse-vertex or source-match premise is supplied. -/
theorem compatibleMeshCurrentRootwardPath_source_margin
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (k : Fin (m + 1)) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖(PathAt[i,fresh,m,length]).vertex k.castSucc - (Q).projectedVertex SourceAt[i]‖ *
        ‖(PathAt[i,fresh,m,length]).edge k‖) ≤
      inner ℝ ((PathAt[i,fresh,m,length]).vertex k.castSucc - (Q).projectedVertex SourceAt[i])
        ((PathAt[i,fresh,m,length]).edge k) := by
  have follows := K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[i] (m + 2) length.ge
  have margin := R.follows_subhistory_radial_margin HistoryAt[i,m] follows positive beta acute
    bpos ratio
    inner_disk upper small 0 ⟨1 + k.val, by omega⟩ (Nat.zero_le _)
  rw [K.compatibleMeshCurrentRootwardPath_eq_history]
  exact margin

/-- Distances from the actual fresh source increase throughout every original parent bank. -/
theorem compatibleMeshCurrentRootwardPath_radialFrom_source
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (PathAt[i,fresh,m,length]).RadialFrom ((Q).projectedVertex SourceAt[i]) 0 := by
  intro k _
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  have margin := K.compatibleMeshCurrentRootwardPath_source_margin compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length k
  exact (mul_nonneg (fine_annular_radial_margin_pos small).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans margin

/-- The actual fresh source already has strict radial progress along every nonzero bank. -/
theorem compatibleMeshCurrentRootwardPath_strictRadialSource
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (Q).projectedVertex SourceAt[i] ∈ (PathAt[i,fresh,m,length]).strictRadialSources :=
  (PathAt[i,fresh,m,length]).strictRadialSource_of_margin
    (fine_annular_radial_margin_pos small)
    (K.compatibleMeshCurrentRootwardPath_radialFrom_source compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side bpos ratio upper small i fresh m length)
    (K.compatibleMeshCurrentRootwardPath_initial_dist_pos compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length)
    (K.compatibleMeshCurrentRootwardPath_source_margin compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side bpos ratio upper small i fresh m length)

/-- All earlier actual bank points have radial order along the complete physical stem. -/
theorem compatibleMeshCurrentRootwardPath_globallyRadiallyMonotone
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (PathAt[i,fresh,m,length]).GloballyRadiallyMonotone :=
  R.follows_globallyRadiallyMonotone PathAt[i,fresh,m,length]
    (K.compatibleMeshCurrentRootwardPath_follows compact nonempty R no_boundary level higher M
      positive
      inner_disk beta acute W r side i fresh m length)
    positive beta acute bpos ratio inner_disk upper small

end Unfoldings.ConvexRoof
