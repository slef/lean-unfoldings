module

public import Unfoldings.Cap.OriginalBankHeadingComparison
public import Unfoldings.Complex.AffineProjectionChains
public import Unfoldings.Development.AffineProjection
public import Unfoldings.Development.AdditionalCuts

/-! The actual projected cut metric realizes the original projected one-sided fan headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- The same selected original faces and seams, measured in their actual planar projection. -/
def projectedCutComplex (U : Set Face) :=
  (C.restrictFaces U).affineProjectionComplex (fun f => K.projectFaceEquiv f.val)
    (fun s x => K.projectedTriangle_joined s.val x)

open Classical in
/-- Every original finite bank chain retains its full labels and successor order in projection. -/
def projectedCutChain (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) :
    ((K.projectedCutComplex U).boundarySystem retain).Chain n :=
  (C.restrictFaces U).affineProjectionChain (fun f => K.projectFaceEquiv f.val)
    (fun s x => K.projectedTriangle_joined s.val x) chain

open Classical in
/-- Identity placement of projected triangles keeps opposite-side hinges for every retained cut. -/
def projectedCutDevelopment (U : Set Face) (retain : Set (C.restrictFaces U).Seam) :
    FacewiseDevelopment (K.projectedCutComplex U) retain :=
  ((C.restrictFaces U).affineProjectionDevelopment (fun f => K.projectFaceEquiv f.val)
    (fun s x => K.projectedTriangle_joined s.val x) (by
      intro f g different
      exact K.projectedTriangles_nonoverlapping (fun same => different (Subtype.ext same)))).cut
        (Set.subset_univ retain)

open Classical in
/-- The numerical projected fan heading is the actual unreduced heading of this metric chain. -/
theorem projectedCutChain_heading (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.projectedCutComplex U).boundaryChainRollHeading (K.projectedCutChain U chain) i =
      K.projectedFanRollHeading U chain i :=
  (C.restrictFaces U).affineProjectionChain_heading (fun f => K.projectFaceEquiv f.val)
    (fun s x => K.projectedTriangle_joined s.val x) chain i

open Classical in
/-- Projected bank lengths are the lengths of the actual physical horizontal bank vectors. -/
theorem projectedCutChain_bankLength (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
    (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.projectedCutComplex U).boundaryBankLength ((K.projectedCutChain U chain).point i) =
      ‖Cap.horizontal ((K.folding.restrictFaces U).germDirection (chain.point i).val)‖ := by
  rw [SpatialFolding.germDirection, map_sub, ← dist_eq_norm]
  rfl

end Unfoldings.ConvexCap
