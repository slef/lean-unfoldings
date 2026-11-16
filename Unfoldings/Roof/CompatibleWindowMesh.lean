module

public import Unfoldings.Roof.CompatibleWindowPatch
public import Unfoldings.Geometry.SpatialEnvelopeWindowPartition
public import Unfoldings.Geometry.SpatialEnvelopeGraphTriangulation
public import Unfoldings.Geometry.SpatialGraphCutIndependence

/-! Match actual finite triangular completion meshes with the original forest-cut window patch. -/

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

local instance windowMeshModelFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance windowMeshIndexFinite : Finite T.Index := T.finite

/-- The actual finite triangular cut and the original window cut are globally isometric.
Only physical domain, height and cut-line geometry are required, not metric or fan certificates. -/
def cutMeshEquiv : V.Patch ≃ᵢ T.graphPartition.Cut R.carrier :=
  (V.whole.partition.windowGraphCutEquiv equations proper V.signs V.aligned full R.carrier).trans
    (((V.whole.partition.windowGraphPartition
      equations proper V.signs V.aligned full).cutPartitionEquiv
      (T.graphPartitionOn (SpatialEnvelope.height M.plane) _ domain heights)
      R.carrier R.isClosed_carrier (fun a => V.whole.carrier_disjoint_interior a.val) outside).trans
        (T.graphPartitionOnCutEquiv
          (SpatialEnvelope.height M.plane) _ domain heights R.carrier).symm)

/-- The finite mesh equivalence retains every original spatial roof point. -/
theorem fold_cutMeshEquiv (x : V.Patch) :
    T.graphPartition.fold R.carrier (V.cutMeshEquiv proper full T domain heights outside x) =
      (V.whole.partition.restoreCut R.carrier
        (V.whole.partition.windowCutMap V.signs R.carrier x)).val := by
  let P := V.whole.partition.windowGraphPartition equations proper V.signs V.aligned full
  let Q := T.graphPartitionOn (SpatialEnvelope.height M.plane) _ domain heights
  let first := V.whole.partition.windowGraphCutEquiv
    equations proper V.signs V.aligned full R.carrier
  let middle := P.cutPartitionEquiv Q R.carrier R.isClosed_carrier
    (fun a => V.whole.carrier_disjoint_interior a.val) outside
  have last (y : Q.Cut R.carrier) : T.graphPartition.fold R.carrier
      ((T.graphPartitionOnCutEquiv
        (SpatialEnvelope.height M.plane) _ domain heights R.carrier).symm y) =
        Q.fold R.carrier y := rfl
  exact (last (middle (first x))).trans
    ((P.fold_cutPartitionEquiv Q R.carrier R.isClosed_carrier
      (fun a => V.whole.carrier_disjoint_interior a.val) outside (first x)).trans
        (V.whole.partition.fold_windowGraphCutEquiv
          equations proper V.signs V.aligned full R.carrier x))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
