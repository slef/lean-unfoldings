module

public import Unfoldings.Roof.CompatibleWindowPairedMesh
public import Unfoldings.Geometry.SpatialEnvelopeWindowFiber

/-! The actual finite triangle inclusion has unique whole-cut fibers in the window interior. -/

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
  (outside : ∀ i, Disjoint (interior (T.projectedTriangle i).carrier) R.carrier)
  (W : R.WholeCutModel M)

local instance pairedFiberModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance pairedFiberOriginalFintype : Fintype W.Index := W.finiteIndex
local instance pairedFiberIndexFinite : Finite T.Index := T.finite

local instance pairedFiberIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (retain : Set T.pairedComplex.Seam)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ R.carrier)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' R.carrier))

/-- No competing finite-mesh copy maps to the same original strict-interior bank copy. -/
theorem pairedMeshMap_injective_at (x : T.pairedComplex.Realization retain)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (T.pairedFolding.toSpace retain x)))
    (y : T.pairedComplex.Realization retain)
    (equal : V.pairedMeshMap proper full T domain heights outside W conforming retain removed
        retained x = V.pairedMeshMap proper full T domain heights outside W conforming retain
          removed retained y) : x = y := by
  let e := (T.pairedCutGraphEquiv conforming retain R.carrier removed retained).trans
    (V.cutMeshEquiv proper full T domain heights outside).symm
  let d := (W.cutModelEquiv V.whole).symm
  let f := V.whole.partition.windowCutMap V.signs R.carrier
  have physical : (V.whole.partition.restoreCut R.carrier (f (e x))).val =
      T.pairedFolding.toSpace retain x :=
    (congrArg PolygonalPoint.val (V.restore_patchMap W (e x))).symm.trans
      (V.restore_pairedMeshMap proper full T domain heights outside W conforming retain
        removed retained x)
  have local_positive : ∀ j, 0 < equations j
      (Cap.horizontal (V.whole.partition.restoreCut R.carrier (f (e x))).val) := by
    intro j
    exact Eq.mpr (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p)) physical)
      (positive j)
  apply e.injective
  exact V.whole.partition.windowCutMap_injective_at equations V.signs V.aligned R.carrier (e x)
    local_positive (e y) (d.injective equal)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
