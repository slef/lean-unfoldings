module

public import Unfoldings.Roof.CompatibleWindowMesh
public import Unfoldings.Metric.LocalChartSourceTransport

/-! Actual finite meshes retain whole neighborhoods of original forest-cut bank copies. -/

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
  (outside : ∀ i, Disjoint (interior (T.projectedTriangle i).carrier) R.carrier)
  (W : R.WholeCutModel M)

local instance windowMeshChartModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance windowMeshChartOriginalFintype : Fintype W.Index := W.finiteIndex
local instance windowMeshChartIndexFinite : Finite T.Index := T.finite

/-- Include the actual finite triangular cut in the original complete forest cut. -/
@[macro_inline] def meshMap (y : T.graphPartition.Cut R.carrier) : W.Cut :=
  V.patchMap W ((V.cutMeshEquiv proper full T domain heights outside).symm y)

/-- The actual finite mesh preserves a whole intrinsic ball around every original interior
bank copy, with the exact original inclusion. No metric or fan matching premise is supplied. -/
theorem exists_mesh_ball_chart (x : W.Cut)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut R.carrier x).val)) :
    ∃ source : T.graphPartition.Cut R.carrier,
      V.meshMap proper full T domain heights outside W source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r),
        ∀ z, (B z).val = V.meshMap proper full T domain heights outside W z.val :=
  exists_ball_chart_isometry_source (V.cutMeshEquiv proper full T domain heights outside)
    (V.patchMap W) x (V.exists_patch_ball_chart W x positive)

/-- The finite triangular inclusion retains the original spatial roof point. -/
theorem restore_meshMap (y : T.graphPartition.Cut R.carrier) :
    (W.partition.restoreCut R.carrier (V.meshMap proper full T domain heights outside W y)).val =
      T.graphPartition.fold R.carrier y :=
  (congrArg PolygonalPoint.val (V.restore_patchMap W _)).trans
    (map_isometry_symm (V.cutMeshEquiv proper full T domain heights outside)
      (fun source => (V.whole.partition.restoreCut R.carrier
        (V.whole.partition.windowCutMap V.signs R.carrier source)).val)
      (T.graphPartition.fold R.carrier)
      (V.fold_cutMeshEquiv proper full T domain heights outside) y)

theorem meshMap_lipschitz : LipschitzWith 1 (V.meshMap proper full T domain heights outside W) := by
  intro x y
  have bound := V.patchMap_lipschitz W
    ((V.cutMeshEquiv proper full T domain heights outside).symm x)
    ((V.cutMeshEquiv proper full T domain heights outside).symm y)
  exact bound.trans_eq (congrArg (fun d : ℝ≥0∞ => (1 : ℝ≥0∞) * d)
    ((V.cutMeshEquiv proper full T domain heights outside).symm.isometry.edist_eq x y))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
