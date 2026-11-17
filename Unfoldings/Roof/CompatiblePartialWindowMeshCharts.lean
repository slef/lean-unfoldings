module

public import Unfoldings.Roof.CompatiblePartialWindowMesh
public import Unfoldings.Metric.LocalChartSourceTransport

/-! Actual finite meshes retain whole neighborhoods for closed partial forest cuts. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  {J : Type} {equations : J → Plane →ᵃ[ℝ] ℝ}
  (V : R.WindowModel M equations) (proper : ∀ j, equations j ≠ 0)
  (full : (interior {z | ∀ j, 0 ≤ equations j z}).Nonempty)
  {I : Type w} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : SpatialEnvelope.Triangulation family Z)
  (domain : {z | ∀ j, 0 ≤ equations j z} = SpatialEnvelope.clip family Z)
  (heights : Set.EqOn (SpatialEnvelope.height M.plane) (SpatialEnvelope.height family)
    {z | ∀ j, 0 ≤ equations j z})
  (cuts : Set Plane) (closed : IsClosed cuts) (included : cuts ⊆ R.carrier)
  (outside : ∀ i, Disjoint (interior (T.projectedTriangle i).carrier) cuts)
  (W : R.WholeCutModel M)

local instance partialWindowMeshChartModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialWindowMeshChartOriginalFintype : Fintype W.Index := W.finiteIndex
local instance partialWindowMeshChartIndexFinite : Finite T.Index := T.finite

/-- Include the actual finite triangular cut in the original complete forest cut. -/
@[macro_inline] def partialMeshMap (y : T.graphPartition.Cut cuts) : W.partition.Cut cuts :=
  V.partialPatchMap W cuts closed included ((V.partialCutMeshEquiv proper full T domain heights
    cuts closed included outside).symm y)

/-- The actual finite mesh preserves a whole intrinsic ball around every original interior
bank copy, with the exact original inclusion. No metric or fan matching premise is supplied. -/
theorem exists_partialMesh_ball_chart (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    ∃ source : T.graphPartition.Cut cuts,
      V.partialMeshMap proper full T domain heights cuts closed included outside W source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r),
        ∀ z, (B z).val = V.partialMeshMap proper full T domain heights cuts closed included
          outside W z.val :=
  exists_ball_chart_isometry_source (V.partialCutMeshEquiv proper full T domain heights cuts
    closed included outside)
    (V.partialPatchMap W cuts closed included) x (V.exists_partialPatch_ball_chart W cuts closed
      included x positive)

/-- The finite triangular inclusion retains the original spatial roof point. -/
theorem restore_partialMeshMap (y : T.graphPartition.Cut cuts) :
    (W.partition.restoreCut cuts (V.partialMeshMap proper full T domain heights cuts closed
      included outside W y)).val =
      T.graphPartition.fold cuts y :=
  (congrArg PolygonalPoint.val (V.restore_partialPatchMap W cuts closed included _)).trans
    (map_isometry_symm (V.partialCutMeshEquiv proper full T domain heights cuts closed included
      outside)
      (fun source => (V.whole.partition.restoreCut cuts
        (V.whole.partition.windowCutMap V.signs cuts source)).val)
      (T.graphPartition.fold cuts)
      (V.fold_partialCutMeshEquiv proper full T domain heights cuts closed included outside) y)

theorem partialMeshMap_lipschitz : LipschitzWith 1 (V.partialMeshMap proper full T domain heights
  cuts closed included outside W) := by
  intro x y
  have bound := V.partialPatchMap_lipschitz W cuts closed included
    ((V.partialCutMeshEquiv proper full T domain heights cuts closed included outside).symm x)
    ((V.partialCutMeshEquiv proper full T domain heights cuts closed included outside).symm y)
  exact bound.trans_eq (congrArg (fun d : ℝ≥0∞ => (1 : ℝ≥0∞) * d)
    ((V.partialCutMeshEquiv proper full T domain heights cuts closed included
      outside).symm.isometry.edist_eq x y))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
