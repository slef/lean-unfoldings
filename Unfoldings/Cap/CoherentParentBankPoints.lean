module

public import Unfoldings.Cap.CompletedBankFaceValues
public import Unfoldings.Cap.ProjectedCoherence
public import Unfoldings.Cap.CompletedForestBanks

/-! Coherent physical points have their actual value on both named completed parent banks. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (R : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C R.retain)

theorem parent_bank_points_eq_of_coherent
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    {s : ℝ} (inside : s ∈ Set.Icc 0 1)
    (coherent : D.ProjectedCoherentAt K
      (AffineMap.lineMap (K.projectedVertex (R.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) s)) :
    R.parentEntrancePoint (R.completedDevelopment D) e s = D.projectedMap K
        (AffineMap.lineMap (K.projectedVertex (R.spanningCompletion.parents.parent e.val))
          (K.projectedVertex e.val) s) ∧
      R.parentExitPoint (R.completedDevelopment D) e s = D.projectedMap K
        (AffineMap.lineMap (K.projectedVertex (R.spanningCompletion.parents.parent e.val))
          (K.projectedVertex e.val) s) := by
  have faces := R.parent_bank_points_mem_faces (R.completedDevelopment D) e inside
  constructor
  · rw [R.parentEntrancePoint_eq_projectedPlacement]
    change D.projectedPlacement K _ _ = D.projectedMap K _
    exact (D.projectedMap_eq_of_coherent K coherent faces.1).symm
  · rw [R.parentExitPoint_eq_projectedPlacement]
    change D.projectedPlacement K _ _ = D.projectedMap K _
    exact (D.projectedMap_eq_of_coherent K coherent faces.2).symm

theorem parent_bank_child_eq_of_coherent
    (e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
    (coherent : D.ProjectedCoherentAt K (K.projectedVertex e.val)) :
    R.parentEntrancePoint (R.completedDevelopment D) e 1 =
        D.projectedMap K (K.projectedVertex e.val) ∧
      R.parentExitPoint (R.completedDevelopment D) e 1 =
        D.projectedMap K (K.projectedVertex e.val) := by
  have at_child : D.ProjectedCoherentAt K
      (AffineMap.lineMap (K.projectedVertex (R.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) (1 : ℝ)) := by
    rwa [AffineMap.lineMap_apply_one]
  simpa only [AffineMap.lineMap_apply_one] using
    R.parent_bank_points_eq_of_coherent D e ⟨zero_le_one, le_rfl⟩ at_child

end Unfoldings.ConvexCap.RadialCutForest
