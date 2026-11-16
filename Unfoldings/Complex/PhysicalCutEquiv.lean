module

public import Unfoldings.Complex.PhysicalCutForward

/-! Original retained triangle complexes and actual physical cuts have the same intrinsic metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  (embedded : F.IsEmbedded) (retain : Set C.Seam) (cuts : Set Space)
  (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    F.place (C.left s).face x.val ∈ cuts)
  (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts)

theorem physicalCutToComplex_complexToPhysicalCut (x : C.Realization retain) :
    F.physicalCutToComplex embedded retain cuts removed
      (F.complexToPhysicalCut retain cuts retained x) = x := by
  obtain ⟨⟨f, p⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  exact congrArg (C.faceMap retain f) ((F.faceImageIsometryEquiv f).symm_apply_apply p)

theorem complexToPhysicalCut_physicalCutToComplex (x : F.PhysicalCut cuts) :
    F.complexToPhysicalCut retain cuts retained
      (F.physicalCutToComplex embedded retain cuts removed x) = x := by
  obtain ⟨⟨f, p⟩, rfl⟩ := MetricGluing.point_surjective (fun f => F.faceImage f)
    (F.physicalCutSeams cuts).relation x
  exact congrArg (MetricGluing.of (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation f)
    ((F.faceImageIsometryEquiv f).apply_symm_apply p)

/-- Geometric removal of whole original edges gives exactly the actual physical cut metric.
Retained open edges avoid the cut; removed closed edges lie in it. Endpoint bank copies and
all original corner classes are retained, with no fan or metric comparison certificate. -/
def complexPhysicalCutEquiv : C.Realization retain ≃ᵢ F.PhysicalCut cuts where
  toFun := F.complexToPhysicalCut retain cuts retained
  invFun := F.physicalCutToComplex embedded retain cuts removed
  left_inv := F.physicalCutToComplex_complexToPhysicalCut embedded retain cuts removed retained
  right_inv := F.complexToPhysicalCut_physicalCutToComplex embedded retain cuts removed retained
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · exact (F.complexToPhysicalCut_lipschitz retain cuts retained x y).trans_eq (one_mul _)
    · have bound := F.physicalCutToComplex_lipschitz embedded retain cuts removed
        (F.complexToPhysicalCut retain cuts retained x)
        (F.complexToPhysicalCut retain cuts retained y)
      exact (congrArg₂ edist
        (F.physicalCutToComplex_complexToPhysicalCut embedded retain cuts removed retained x)
        (F.physicalCutToComplex_complexToPhysicalCut embedded retain cuts removed retained y)).symm
        |>.trans_le (bound.trans_eq (one_mul _))

/-- The metric isometry keeps every original triangle copy in its original physical face. -/
@[simp] theorem complexPhysicalCutEquiv_faceMap (f : Face) (x : C.Cell f) :
    F.complexPhysicalCutEquiv embedded retain cuts removed retained (C.faceMap retain f x) =
      F.faceMapToPhysicalCut cuts f x := rfl

/-- The original spatial folding is unchanged by the exact physical-cut identification. -/
theorem fold_complexPhysicalCutEquiv (x : C.Realization retain) :
    (F.physicalCutSeams cuts).fold
      (F.complexPhysicalCutEquiv embedded retain cuts removed retained x) = F.toSpace retain x := by
  obtain ⟨⟨f, p⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  rfl

end Unfoldings.SpatialFolding
