module

public import Unfoldings.Complex.SeamFaceRoute

/-! Lift actual face-contained route pieces continuously into their original closed faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

def faceRangeEquiv (retain : Set C.Seam) (f : Face) :
    C.Cell f ≃ᵢ Set.range (C.faceMap retain f) :=
  (F.faceMap_isometry retain f).isometryEquivOnRange

def faceRoutePiecePath {a b : C.Realization Set.univ} {p : Path a b}
    (R : C.FaceRoute p) (i : Fin R.steps) : Path (R.entry i) (R.exit i) := by
  let H := F.faceRangeEquiv Set.univ (R.face i)
  have inside (t : unitInterval) : p (Path.intervalParam (R.time i.castSucc) (R.time i.succ) t) ∈
      Set.range (C.faceMap Set.univ (R.face i)) :=
    R.inside i _ (Path.intervalParam_mem_Icc (R.increasing Fin.castSucc_lt_succ).le t)
  refine
    { toFun := fun t => H.symm
        ⟨p (Path.intervalParam (R.time i.castSucc) (R.time i.succ) t), inside t⟩
      continuous_toFun := H.symm.isometry.continuous.comp
        ((p.continuous.comp (Path.continuous_intervalParam _ _)).subtype_mk inside)
      source' := ?_
      target' := ?_ }
  · apply H.injective
    rw [H.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg p (Path.intervalParam_zero _ _)).trans (R.entry_image i).symm
  · apply H.injective
    rw [H.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg p (Path.intervalParam_one _ _)).trans (R.exit_image i).symm

theorem faceRoutePiecePath_image {a b : C.Realization Set.univ} {p : Path a b}
    (R : C.FaceRoute p) (i : Fin R.steps) (t : unitInterval) :
    C.faceMap Set.univ (R.face i) (F.faceRoutePiecePath R i t) =
      p (Path.intervalParam (R.time i.castSucc) (R.time i.succ) t) := by
  let H := F.faceRangeEquiv Set.univ (R.face i)
  exact congrArg Subtype.val (H.apply_symm_apply _)

end Unfoldings.SpatialFolding
