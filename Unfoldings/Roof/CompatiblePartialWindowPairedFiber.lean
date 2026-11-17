module

public import Unfoldings.Roof.CompatiblePartialWindowPairedMesh
public import Unfoldings.Geometry.SpatialEnvelopeWindowFiber

/-! Finite partial-cut inclusions have unique whole-cut fibers in the window interior. -/

@[expose] public section

noncomputable section

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

local instance partialPairedFiberModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialPairedFiberOriginalFintype : Fintype W.Index := W.finiteIndex
local instance partialPairedFiberIndexFinite : Finite T.Index := T.finite

local instance partialPairedFiberIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (retain : Set T.pairedComplex.Seam)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))

/-- No competing finite-mesh copy maps to the same original strict-interior bank copy. -/
theorem partialPairedMeshMap_injective_at (x : T.pairedComplex.Realization retain)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (T.pairedFolding.toSpace retain x)))
    (y : T.pairedComplex.Realization retain)
    (equal : V.partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained x =
      V.partialPairedMeshMap proper full T domain heights cuts closed included outside W conforming
        retain removed retained y) : x = y := by
  let e := (T.pairedCutGraphEquiv conforming retain cuts removed retained).trans
    (V.partialCutMeshEquiv proper full T domain heights cuts closed included outside).symm
  let d := (W.partialCutModelEquiv V.whole cuts closed included).symm
  let f := V.whole.partition.windowCutMap V.signs cuts
  have physical : (V.whole.partition.restoreCut cuts (f (e x))).val =
      T.pairedFolding.toSpace retain x :=
    (congrArg PolygonalPoint.val
      (V.restore_partialPatchMap W cuts closed included (e x))).symm.trans
      (V.restore_partialPairedMeshMap proper full T domain heights cuts closed included outside W
        conforming retain removed retained x)
  have local_positive : ∀ j, 0 < equations j
      (Cap.horizontal (V.whole.partition.restoreCut cuts (f (e x))).val) := by
    intro j
    exact Eq.mpr (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p)) physical)
      (positive j)
  apply e.injective
  exact V.whole.partition.windowCutMap_injective_at equations V.signs V.aligned cuts (e x)
    local_positive (e y) (d.injective equal)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
