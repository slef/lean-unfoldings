module

public import Unfoldings.Roof.CompatibleMeshWindowCharts
public import Unfoldings.Roof.CompatibleWindowPairedCenters
public import Unfoldings.Cone.TransportedCharts

/-! Actual original corner-fan neighborhoods in the complete forest cut. -/

@[expose] public section

noncomputable section

open scoped ENNReal

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

local instance compatibleCornerIndexFintype : Fintype (T).Index :=
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
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance compatibleCornerWholeFintype : Fintype W.Index := W.finiteIndex

/-- A specified original finite-mesh bank copy retains its whole neighborhood in the
original full forest cut, with its exact original inclusion and spatial folding. -/
theorem compatibleMesh_ball_chart_at (y : (T).pairedComplex.Realization (Fcut).retain)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain y)) < level) :
    ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball y (ENNReal.ofReal r) ≃ᵢ
      Metric.eball
        (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W y) (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W z.val := by
  apply (V).pairedMesh_ball_chart_at proper full (T).toTriangulation domain heights outside
    W conforming (Fcut).retain removed retained y
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

/-- Every specified finite retained corner strictly below the completion level has its
actual original tangent fan in the whole forest cut, with every original face coordinate.
The fan and its angle are constructed from the original retained triangle corners. -/
theorem compatibleMesh_corner_fan_chart (vertex : (T).pairedComplex.Vertex (Fcut).retain)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
        ((T).pairedComplex.vertexPoint (Fcut).retain vertex))) < level) :
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball ((T).pairedComplex.tangentOrigin (Fcut).retain vertex)
        (ENNReal.ofReal r) ≃ᵢ
        Metric.eball
          (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W ((T).pairedComplex.vertexPoint (Fcut).retain vertex))
          (ENNReal.ofReal r),
        ∀ (a : (T).pairedComplex.TangentTotal (Fcut).retain vertex)
          (near : edist ((T).pairedComplex.tangentPoint (Fcut).retain vertex a)
            ((T).pairedComplex.tangentOrigin (Fcut).retain vertex) < ENNReal.ofReal r),
          (chart ⟨(T).pairedComplex.tangentPoint (Fcut).retain vertex a, near⟩).val =
            K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
              inner_disk beta acute W
              ((T).pairedComplex.tangentSurfaceTag (Fcut).retain vertex a) :=
  (T).pairedFolding.exists_tangentChart_of_localMap (Fcut).retain vertex
    (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W)
    (K.compatibleMesh_ball_chart_at compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W _ below)

end Unfoldings.ConvexRoof
