module

public import Unfoldings.Roof.CompatiblePartialWindowPairedMesh
public import Unfoldings.Geometry.SpatialEnvelopeWindowCenters

/-! Exact whole neighborhoods at specified intermediate finite-mesh corner and bank copies. -/

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

local instance partialPairedCenterModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialPairedCenterOriginalFintype : Fintype W.Index := W.finiteIndex
local instance partialPairedCenterIndexFinite : Finite T.Index := T.finite

local instance partialPairedCenterIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (retain : Set T.pairedComplex.Seam)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))

/-- A specified retained finite-mesh copy strictly inside the window has its own whole
original-cut neighborhood. The center is the actual chosen copy, including at vertices. -/
theorem partialPairedMesh_ball_chart_at (y : T.pairedComplex.Realization retain)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (T.pairedFolding.toSpace retain y))) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball y (ENNReal.ofReal r) ≃ᵢ
      Metric.eball
        (V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
          conforming retain removed retained y)
        (ENNReal.ofReal r), ∀ z, (B z).val =
          V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
            conforming retain removed retained z.val := by
  let e := (T.pairedCutGraphEquiv conforming retain cuts removed retained).trans
    (V.partialCutMeshEquiv proper full T domain heights cuts closed included outside).symm
  let d := (W.partialCutModelEquiv V.whole cuts closed included).symm
  let f := V.whole.partition.windowCutMap V.signs cuts
  have physical : (V.whole.partition.restoreCut cuts (f (e y))).val =
      T.pairedFolding.toSpace retain y :=
    (congrArg PolygonalPoint.val
      (V.restore_partialPatchMap W cuts closed included (e y))).symm.trans
      (V.restore_partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained y)
  have local_positive : ∀ j, 0 < equations j
      (Cap.horizontal (V.whole.partition.restoreCut cuts (f (e y))).val) := by
    intro j
    exact Eq.mpr (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p)) physical)
      (positive j)
  exact centered_ball_chart_isometries e.symm d f y
    (V.whole.partition.windowCut_ball_chart_at equations V.signs V.aligned cuts
      (e y) local_positive)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
