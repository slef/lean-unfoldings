module

public import Unfoldings.Roof.CompatiblePartialWindowPairedMesh
public import Unfoldings.Roof.CompatiblePartialWindowPairedFiber
public import Unfoldings.Metric.LocalIsometricLift
public import Unfoldings.Metric.ContinuousChartLift

/-! Canonical finite lifts of actual partial-cut copies and curves. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

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

local instance partialPairedLiftModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialPairedLiftOriginalFintype : Fintype W.Index := W.finiteIndex
local instance partialPairedLiftIndexFinite : Finite T.Index := T.finite

local instance partialPairedLiftIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (retain : Set T.pairedComplex.Seam)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))

/-- Every whole partial-cut copy strictly inside the window has one uniquely determined
finite-mesh copy. Uniqueness includes preimages outside any chosen local chart. -/
theorem existsUnique_partialPairedMesh_preimage (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    ∃! y : T.pairedComplex.Realization retain,
      V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained y = x := by
  obtain ⟨y, image, _chart⟩ := V.exists_partialPairedMesh_ball_chart proper full T domain heights
    cuts closed included outside W conforming retain removed retained x positive
  have physical : T.pairedFolding.toSpace retain y = (W.partition.restoreCut cuts x).val :=
    (V.restore_partialPairedMeshMap proper full T domain heights cuts closed included outside W
      conforming retain removed retained y).symm.trans
        (congrArg (fun z => (W.partition.restoreCut cuts z).val) image)
  have source_positive : ∀ j, 0 < equations j
      (Cap.horizontal (T.pairedFolding.toSpace retain y)) := by
    intro j
    exact Eq.mpr (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p)) physical)
      (positive j)
  refine ⟨y, image, fun z at_z => ?_⟩
  exact (V.partialPairedMeshMap_injective_at proper full T domain heights cuts closed included
    outside W conforming retain removed retained y source_positive z
      (image.trans at_z.symm)).symm

/-- Choose the finite copy only after its original whole-cut fiber is proved unique. -/
def partialPairedMeshLift (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    T.pairedComplex.Realization retain :=
  (V.existsUnique_partialPairedMesh_preimage proper full T domain heights cuts closed included
    outside W conforming retain removed retained x positive).choose

/-- The lift retains the literal original whole-cut copy, including its bank label. -/
@[simp] theorem partialPairedMeshMap_lift (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    V.partialPairedMeshMap proper full T domain heights cuts closed included outside W conforming
      retain removed retained
      (V.partialPairedMeshLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained x positive) = x :=
  (V.existsUnique_partialPairedMesh_preimage proper full T domain heights cuts closed included
    outside W conforming retain removed retained x positive).choose_spec.1

/-- Every finite copy with the prescribed whole-cut image is the canonical lift. -/
theorem partialPairedMeshLift_unique (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val))
    (y : T.pairedComplex.Realization retain)
    (image : V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
      conforming retain removed retained y = x) :
    y = V.partialPairedMeshLift proper full T domain heights cuts closed included outside W
      conforming retain removed retained x positive :=
  (V.existsUnique_partialPairedMesh_preimage proper full T domain heights cuts closed included
    outside W conforming retain removed retained x positive).choose_spec.2 y image

/-- Lifting keeps the original spatial point and its full metric bank copy. -/
theorem partialPairedMeshLift_toSpace (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    T.pairedFolding.toSpace retain
      (V.partialPairedMeshLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained x positive) =
      (W.partition.restoreCut cuts x).val := by
  have image := V.partialPairedMeshMap_lift proper full T domain heights cuts closed included
    outside W conforming retain removed retained x positive
  exact (V.restore_partialPairedMeshMap proper full T domain heights cuts closed included outside W
    conforming retain removed retained _).symm.trans
      (congrArg (fun z => (W.partition.restoreCut cuts z).val) image)

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (s : Set A)
  (g : s → W.partition.Cut cuts)
  (positive : ∀ t j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts (g t)).val))

/-- Lift an entire curve to the uniquely determined finite copies of the same partial cut. -/
def partialPairedMeshCurveLift : s → T.pairedComplex.Realization retain :=
  fun t => V.partialPairedMeshLift proper full T domain heights cuts closed included outside W
    conforming retain removed retained (g t) (positive t)

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
@[simp] theorem partialPairedMeshMap_curveLift (t : s) :
    V.partialPairedMeshMap proper full T domain heights cuts closed included outside W conforming
      retain removed retained
      (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained s g positive t) = g t :=
  V.partialPairedMeshMap_lift proper full T domain heights cuts closed included outside W
    conforming retain removed retained (g t) (positive t)

/-- Actual local charts and unique whole fibers preserve the original common Lipschitz
constant on a convex curve parameter domain. No global mesh isometry is assumed. -/
theorem partialPairedMeshCurveLift_lipschitz (convex : Convex ℝ s) {c : ℝ≥0}
    (bounded : LipschitzWith c g) : LipschitzWith c
      (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained s g positive) := by
  let f := V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
    conforming retain removed retained s g positive
  let F := V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
    conforming retain removed retained
  apply lipschitzWith_lift_of_ball_charts s convex f g F c bounded
  · intro t x image
    exact V.partialPairedMeshLift_unique proper full T domain heights cuts closed included outside W
      conforming retain removed retained (g t) (positive t) x image
  · intro t
    obtain ⟨z, image, r, rpos, chart, agrees⟩ := V.exists_partialPairedMesh_ball_chart proper full T
      domain heights cuts closed included outside W conforming retain removed retained (g t)
      (positive t)
    have same : z = f t := V.partialPairedMeshLift_unique proper full T domain heights cuts closed
      included outside W conforming retain removed retained (g t) (positive t) z image
    subst z
    exact ⟨r, rpos, chart, agrees⟩

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- Canonical whole-copy lifts preserve continuity without any curve speed assumption. -/
theorem partialPairedMeshCurveLift_continuous [TopologicalSpace A]
    (continuous : Continuous g) : Continuous
      (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained s g positive) := by
  let f := V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
    conforming retain removed retained s g positive
  let F := V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
    conforming retain removed retained
  apply continuous_lift_of_ball_charts f g F continuous
  · intro t x image
    exact V.partialPairedMeshLift_unique proper full T domain heights cuts closed included outside W
      conforming retain removed retained (g t) (positive t) x image
  · intro t
    obtain ⟨z, image, r, rpos, chart, agrees⟩ := V.exists_partialPairedMesh_ball_chart proper full T
      domain heights cuts closed included outside W conforming retain removed retained (g t)
      (positive t)
    have same : z = f t := V.partialPairedMeshLift_unique proper full T domain heights cuts closed
      included outside W conforming retain removed retained (g t) (positive t) z image
    subst z
    exact ⟨r, rpos, chart, agrees⟩

/-- Lifting an original dilation preserves every pairwise intrinsic distance on a convex
parameter domain. The lower bound comes from the actual nonexpanding whole-cut inclusion. -/
theorem edist_partialPairedMeshCurveLift_dilation (convex : Convex ℝ s)
    (h : s →ᵈ W.partition.Cut cuts)
    (interior_h : ∀ t j, 0 < equations j
      (Cap.horizontal (W.partition.restoreCut cuts (h t)).val)) (x y : s) :
    edist
      (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained s h interior_h x)
      (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
        conforming retain removed retained s h interior_h y) = edist (h x) (h y) := by
  have upper := V.partialPairedMeshCurveLift_lipschitz proper full T domain heights cuts closed
    included outside W conforming retain removed retained s h interior_h convex
    (Dilation.lipschitzWith h)
  apply le_antisymm ((upper x y).trans_eq (Dilation.edist_eq h x y).symm)
  have lower := V.partialPairedMeshMap_lipschitz proper full T domain heights cuts closed included
    outside W conforming retain removed retained
    (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
      conforming retain removed retained s h interior_h x)
    (V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
      conforming retain removed retained s h interior_h y)
  simpa only [V.partialPairedMeshMap_curveLift, ENNReal.coe_one, one_mul] using lower

/-- The original metric dilation itself lifts to the actual finite partial-cut mesh. -/
def partialPairedMeshCurveLiftDilation (convex : Convex ℝ s)
    (h : s →ᵈ W.partition.Cut cuts)
    (interior_h : ∀ t j, 0 < equations j
      (Cap.horizontal (W.partition.restoreCut cuts (h t)).val)) :
    s →ᵈ T.pairedComplex.Realization retain where
  toFun := V.partialPairedMeshCurveLift proper full T domain heights cuts closed included outside W
    conforming retain removed retained s h interior_h
  edist_eq' := ⟨Dilation.ratio h, Dilation.ratio_ne_zero h, fun x y =>
    (V.edist_partialPairedMeshCurveLift_dilation proper full T domain heights cuts closed included
      outside W conforming retain removed retained s convex h interior_h x y).trans
        (Dilation.edist_eq h x y)⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
