module

public import Unfoldings.Complex.SubdivisionPhysicalCut
public import Unfoldings.Complex.SubdivisionMetric

/-! Physical cut geometry derives retained seam correspondence for rigid subdivisions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (S : C.Subdivision D) (F : SpatialFolding C) (G : SpatialFolding D)
  (spatial : ∀ g x, F.place (S.parent g) (S.place g x) = G.place g x)
  (cuts : Set Space) (closed : IsClosed cuts)
  (outside : ∀ f, Disjoint (interior (C.triangle f).carrier) (F.place f ⁻¹' cuts))
  (embedded : F.IsEmbedded) (fineEmbedded : G.IsEmbedded)
  (retain : Set C.Seam) (fineRetain : Set D.Seam)
  (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    F.place (C.left s).face x.val ∈ cuts)
  (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts)
  (fineRemoved : ∀ s, s ∉ fineRetain →
    ∀ x : (D.triangle (D.left s).face).Edge (D.left s).edge, G.place (D.left s).face x.val ∈ cuts)
  (fineKept : ∀ s ∈ fineRetain, Disjoint (G.openSeamImage s) cuts)

/-- The canonical original-parent map on actual intrinsic cut spaces, from physical geometry. -/
def physicalCutEquiv : D.Realization fineRetain ≃ᵢ C.Realization retain :=
  ((G.complexPhysicalCutEquiv fineEmbedded fineRetain cuts fineRemoved fineKept).trans
    ((S.physicalCutRefinement F G spatial cuts closed outside).isometryEquiv
      (fun f => (F.compact_faceImage f).isClosed))).trans
        (F.complexPhysicalCutEquiv embedded retain cuts removed retained).symm

theorem physicalCutEquiv_faceMap (g : Child) (y : D.Cell g) :
    S.physicalCutEquiv F G spatial cuts closed outside embedded fineEmbedded retain fineRetain
      removed retained fineRemoved fineKept (D.faceMap fineRetain g y) =
        C.faceMap retain (S.parent g) (S.parentCell g y) := by
  let old := F.complexPhysicalCutEquiv embedded retain cuts removed retained
  let fine := G.complexPhysicalCutEquiv fineEmbedded fineRetain cuts fineRemoved fineKept
  let changeMesh := (S.physicalCutRefinement F G spatial cuts closed outside).isometryEquiv
    (fun f => (F.compact_faceImage f).isClosed)
  apply old.injective
  change old (old.symm (changeMesh (fine (D.faceMap fineRetain g y)))) = _
  exact (old.apply_symm_apply _).trans
    (S.physicalCutRefinement_of F G spatial cuts closed outside g y)

include F G spatial cuts closed outside embedded fineEmbedded removed retained fineRemoved
  fineKept in
/-- Rigid face subdivision and actual geometric edge cuts imply exact retained seam correspondence.
No seam-chain matching or metric comparison is assumed. -/
theorem conforming_of_physicalCuts : S.Conforming retain fineRetain := by
  let E := S.physicalCutEquiv F G spatial cuts closed outside embedded fineEmbedded retain
    fineRetain
    removed retained fineRemoved fineKept
  apply S.conforming_of_injective_pointMap E E.injective
  rintro ⟨g, y⟩
  exact S.physicalCutEquiv_faceMap F G spatial cuts closed outside embedded fineEmbedded retain
    fineRetain removed retained fineRemoved fineKept g y

end Unfoldings.TriangleComplex.Subdivision
