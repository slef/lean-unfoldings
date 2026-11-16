module

public import Unfoldings.Roof.SpatialEnvelopeRoof
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.DiskBoundaryQuotient

/-! Every original metric copy over an actual removed original seam lies on the cut boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance cutBoundaryFiberIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- An original removed edge contributes every original cut copy at its projected points
to the actual intrinsic boundary, even when the copies have different face tags. -/
theorem mem_bankBoundary_of_projected_cut_edge
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (retain : Set T.pairedComplex.Seam) (s : T.pairedComplex.Seam) (removed : s ∉ retain)
    (q : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge) (x : T.pairedComplex.Realization retain)
    (position : Cap.horizontal (T.pairedFolding.toSpace retain x) =
      Cap.horizontal (T.pairedFolding.place (T.pairedComplex.left s).face q.val)) :
    x ∈ T.pairedComplex.bankBoundary retain := by
  let C := T.pairedComplex
  let F := T.pairedFolding
  let included := Set.subset_univ retain
  let source := C.bankMap retain (C.leftBank retain s removed) q
  have on_boundary : source ∈ C.bankBoundary retain := C.bankMap_mem_bankBoundary _ _ _
  have projected : Cap.horizontal (F.toSpace retain source) = Cap.horizontal (F.toSpace retain x) :=
    position.symm
  have same := T.pairedProjection_injective conforming
    ((congrArg Cap.horizontal (F.toSpace_forgetCuts included source)).trans
      (projected.trans (congrArg Cap.horizontal (F.toSpace_forgetCuts included x)).symm))
  rcases C.forgetCuts_fiber_eq_or_boundary included source x same with equal | both
  · exact equal ▸ on_boundary
  · exact both.2

end Unfoldings.SpatialEnvelope.Triangulation
