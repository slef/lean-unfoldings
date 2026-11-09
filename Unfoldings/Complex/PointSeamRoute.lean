module

public import Unfoldings.Complex.PointFiber

/-! Actual bounded seam words through the face copies of one surface point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

structure PointSeamRoute (retain : Set C.Seam) (x : C.Realization retain)
    (a b : C.PointFiber retain x) where
  steps : ℕ
  copy : Fin (steps + 1) → C.PointFiber retain x
  start : copy 0 = a
  finish : copy (Fin.last steps) = b
  seam : Fin steps → C.Seam
  kept : ∀ i, seam i ∈ retain
  side : Fin steps → Bool
  crossing : ∀ i, ∃ q : (C.triangle (C.seamSide (seam i) (side i)).face).Edge
      (C.seamSide (seam i) (side i)).edge,
    (copy i.castSucc).val = C.edgePoint (C.seamSide (seam i) (side i)) q ∧
      (copy i.succ).val = C.edgePoint (C.seamSide (seam i) (!(side i)))
        (C.across (seam i) (side i) q)

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F

theorem exists_short_pointSeamRoute (retain : Set C.Seam) (x : C.Realization retain)
    (a b : C.PointFiber retain x) :
    ∃ R : C.PointSeamRoute retain x a b, R.steps < Fintype.card Face := by
  obtain ⟨p, short⟩ := F.exists_short_pointFiber_path retain x a b
  let copy (i : Fin (p.val.length + 1)) := p.val.getVert i.val
  have crosses (i : Fin p.val.length) : C.Crosses retain
      (copy i.castSucc).val (copy i.succ).val :=
    ((C.pointFiberGraph_adj_iff retain x _ _).mp (p.val.adj_getVert_succ i.isLt)).2
  choose seam kept side point first last using crosses
  exact ⟨{ steps := p.val.length
           copy := copy
           start := p.val.getVert_zero
           finish := p.val.getVert_length
           seam := seam
           kept := kept
           side := side
           crossing := fun i => ⟨point i, first i, last i⟩ }, short⟩

end Unfoldings.SpatialFolding
