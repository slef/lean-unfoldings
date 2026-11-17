module

public import Unfoldings.Roof.CompatiblePartialWindowMeshCharts
public import Unfoldings.Geometry.SpatialEnvelopePhysicalCut

/-! Original paired meshes give whole charts at every closed partial forest cut. -/

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

local instance partialPairedWindowModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialPairedWindowOriginalFintype : Fintype W.Index := W.finiteIndex
local instance partialPairedWindowIndexFinite : Finite T.Index := T.finite

local instance partialPairedWindowMeshIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (retain : Set T.pairedComplex.Seam)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))

/-- Include the original retained triangle complex in the complete forest cut. -/
@[macro_inline] def partialPairedMeshMap (y : T.pairedComplex.Realization retain) :
  W.partition.Cut cuts :=
  V.partialMeshMap proper full T domain heights cuts closed included outside W
    (T.pairedCutGraphEquiv conforming retain cuts removed retained y)

/-- Every original interior metric bank copy has a whole neighborhood in the actual paired
triangle complex. In particular its corner classes are the original retained corner classes. -/
theorem exists_partialPairedMesh_ball_chart (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    ∃ source : T.pairedComplex.Realization retain,
      V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained
        source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r),
        ∀ z, (B z).val =
          V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
            conforming retain removed retained
            z.val :=
  exists_ball_chart_isometry_source
    (T.pairedCutGraphEquiv conforming retain cuts removed retained).symm
    (V.partialMeshMap proper full T domain heights cuts closed included outside W) x
    (V.exists_partialMesh_ball_chart proper full T domain heights cuts closed included outside W
      x positive)

/-- A paired finite-mesh chart folds to its literal original spatial point. -/
theorem restore_partialPairedMeshMap (y : T.pairedComplex.Realization retain) :
    (W.partition.restoreCut cuts
      (V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained
        y)).val = T.pairedFolding.toSpace retain y :=
  (V.restore_partialMeshMap proper full T domain heights cuts closed included outside W _).trans
    (T.fold_pairedCutGraphEquiv conforming retain cuts removed retained y)

theorem partialPairedMeshMap_lipschitz :
    LipschitzWith 1 (V.partialPairedMeshMap proper full T domain heights cuts closed included
      outside W conforming retain
      removed retained) := by
  intro x y
  have bound := V.partialMeshMap_lipschitz proper full T domain heights cuts closed included
    outside W
    (T.pairedCutGraphEquiv conforming retain cuts removed retained x)
    (T.pairedCutGraphEquiv conforming retain cuts removed retained y)
  exact bound.trans_eq (congrArg (fun d : ℝ≥0∞ => (1 : ℝ≥0∞) * d)
    ((T.pairedCutGraphEquiv conforming retain cuts removed retained).isometry.edist_eq x y))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
