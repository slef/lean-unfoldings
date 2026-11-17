module

public import Unfoldings.Roof.CompatiblePartialWindowPatch
public import Unfoldings.Geometry.SpatialEnvelopeWindowPartition
public import Unfoldings.Geometry.SpatialEnvelopeGraphTriangulation
public import Unfoldings.Geometry.SpatialGraphCutIndependence

/-! Match actual finite meshes with closed partial forest-cut windows. -/

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

local instance partialWindowMeshModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialWindowMeshIndexFinite : Finite T.Index := T.finite

/-- The actual finite triangular cut and the original partial window cut are globally isometric.
Only physical domain, height and cut-line geometry are required, not metric or fan certificates. -/
def partialCutMeshEquiv : V.PartialPatch cuts ≃ᵢ T.graphPartition.Cut cuts :=
  (V.whole.partition.windowGraphCutEquiv equations proper V.signs V.aligned full cuts).trans
    (((V.whole.partition.windowGraphPartition
      equations proper V.signs V.aligned full).cutPartitionEquiv
      (T.graphPartitionOn (SpatialEnvelope.height M.plane) _ domain heights)
      cuts closed (fun a => (V.whole.carrier_disjoint_interior a.val).mono_right included)
        outside).trans
        (T.graphPartitionOnCutEquiv
          (SpatialEnvelope.height M.plane) _ domain heights cuts).symm)

/-- The finite mesh equivalence retains every original spatial roof point. -/
theorem fold_partialCutMeshEquiv (x : V.PartialPatch cuts) :
    T.graphPartition.fold cuts (V.partialCutMeshEquiv proper full T domain heights cuts closed
      included outside x) =
      (V.whole.partition.restoreCut cuts
        (V.whole.partition.windowCutMap V.signs cuts x)).val := by
  let P := V.whole.partition.windowGraphPartition equations proper V.signs V.aligned full
  let Q := T.graphPartitionOn (SpatialEnvelope.height M.plane) _ domain heights
  let first := V.whole.partition.windowGraphCutEquiv
    equations proper V.signs V.aligned full cuts
  let middle := P.cutPartitionEquiv Q cuts closed
    (fun a => (V.whole.carrier_disjoint_interior a.val).mono_right included) outside
  have last (y : Q.Cut cuts) : T.graphPartition.fold cuts
      ((T.graphPartitionOnCutEquiv
        (SpatialEnvelope.height M.plane) _ domain heights cuts).symm y) =
        Q.fold cuts y := rfl
  exact (last (middle (first x))).trans
    ((P.fold_cutPartitionEquiv Q cuts closed
      (fun a => (V.whole.carrier_disjoint_interior a.val).mono_right included) outside (first
        x)).trans
        (V.whole.partition.fold_windowGraphCutEquiv
          equations proper V.signs V.aligned full cuts x))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
