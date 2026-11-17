module

public import Unfoldings.Roof.CompatibleMeshRootwardGeometry
public import Unfoldings.Geometry.SupportedRayWindowClosure

/-! Construct supported generic closures of actual rootward bank windows. -/

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

local instance rootwardWindowIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardWindowWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "WindowAt[" j "," h "," k "," hk "," f "," l "," hf "]" =>
  PolygonalChain.interval (K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side j h k hk) f (l + 2) hf

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
  (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

/-- Every short source-ray window of the actual current stem has a constructed generic
supported Jordan closure. All internal original corners remain, and the closing links
avoid every original mesh vertex except their permitted endpoints. -/
theorem exists_compatibleMeshRootwardWindow_supported_closure
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (first n : ℕ) (fits : first + (n + 2) ≤ m + 1)
    (window_small : (∑ k : Fin n, InnerProductGeometry.angle
      ((WindowAt[i,fresh,m,length,first,n,fits]).internalSourceRay
        ((Q).projectedVertex SourceAt[i]) k.castSucc)
      ((WindowAt[i,fresh,m,length,first,n,fits]).internalSourceRay
        ((Q).projectedVertex SourceAt[i]) k.succ)) < Real.pi / 4)
    {δ : ℝ} (room : 0 < δ) :
    ∃ s t : unitInterval, (0 < s.val ∧ s.val < 1) ∧ (0 < t.val ∧ t.val < 1) ∧
      ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        let P := (WindowAt[i,fresh,m,length,first,n,fits]).trimEnds s t
        dist q ((Q).projectedVertex SourceAt[i]) < δ ∧ P.RadialFrom q 0 ∧
        0 < dist q (P.vertex 0) ∧ dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 2))) ∧
        (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (P.vertex (Fin.last (n + 2)) - q) (c - P.vertex (Fin.last (n + 2))) ∧
        (∀ j, K.compatibleCutEquations compact nonempty R no_boundary level higher j q ≠ 0 ∧
          K.compatibleCutEquations compact nonempty R no_boundary level higher j c ≠ 0) ∧
        (∀ v, q ≠ (Q).projectedVertex v ∧ c ≠ (Q).projectedVertex v) ∧
        (∀ v, (Q).projectedVertex v ∈ segment ℝ (P.vertex 0) q →
          (Q).projectedVertex v = P.vertex 0) ∧
        (∀ v, (Q).projectedVertex v ∉ segment ℝ q c) ∧
        (∀ v, (Q).projectedVertex v ∈ segment ℝ (P.vertex (Fin.last (n + 2))) c →
          (Q).projectedVertex v = P.vertex (Fin.last (n + 2))) ∧
        Schoenflies.IsJordanCurve (P.threeSegmentClosure q c) := by
  have strict := K.compatibleMeshCurrentRootwardPath_strictRadialSource compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side bpos ratio upper small
    i fresh m length
  have window_strict : (Q).projectedVertex SourceAt[i] ∈
      (WindowAt[i,fresh,m,length,first,n,fits]).strictRadialSources := by
    intro k nonzero
    exact strict ⟨first + k.val, by omega⟩ nonzero
  have initial : 0 < dist ((Q).projectedVertex SourceAt[i])
      ((WindowAt[i,fresh,m,length,first,n,fits]).vertex 0) := by
    apply dist_pos.mpr
    intro same
    exact K.compatibleMeshCurrentRootwardPath_vertex_ne_source compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length ⟨first, by omega⟩
      (sub_eq_zero.mpr same.symm)
  apply PolygonalChain.exists_supported_vertex_avoiding_ray_window_closure
    (WindowAt[i,fresh,m,length,first,n,fits])
    ((Q).projectedVertex SourceAt[i]) window_strict initial
    (K.compatibleMeshCurrentRootwardPath_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length ⟨first + (n + 1), by omega⟩)
    (fun k => K.compatibleMeshCurrentRootwardPath_vertex_ne_source compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length
      ⟨first + (k.val + 1), by omega⟩) window_small
    (Q).projectedVertex (K.compatibleCutEquations compact nonempty R no_boundary level higher)
    (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher) room

end Unfoldings.ConvexRoof
