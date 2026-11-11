module

public import Unfoldings.Cap.ParentBankNoncrossing

/-! The matched parameters are exactly the actual straight parent-bank segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (D : FacewiseDevelopment C M.retain)

theorem parentEntrancePoint_eq_lineMap
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) :
    M.parentEntrancePoint D e s = AffineMap.lineMap
      (D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).enter))
      (D.boundaryPosition (C.boundaryTurn M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D e).enter))) s := by
  rw [AffineMap.lineMap_apply_module', ← D.boundaryRay_eq_positions,
    (M.parentBankOpening D e).entrance_ray, smul_neg]
  change _ - _ = -_ + _
  abel

theorem parentExitPoint_eq_lineMap
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s : ℝ) :
    M.parentExitPoint D e s = AffineMap.lineMap
      (D.boundaryPosition (C.boundaryTurn M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)))
      (D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)) s := by
  have reverse : D.boundaryPosition (M.projectionContour.cycle.point
      (M.parentBankOpening D e).leave) - D.boundaryPosition (C.boundaryTurn M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)) =
      -M.parentExitVector D e := by
    rw [← neg_sub, ← D.boundaryRay_eq_positions, (M.parentBankOpening D e).exit_ray]
    rfl
  rw [AffineMap.lineMap_apply_module', reverse, smul_neg]
  change _ - _ = -_ + _
  abel

/-- All parameters in the unit interval lie on the actual entrance bank segment. -/
theorem parentEntrancePoint_mem_segment
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) {s : ℝ} (inside : s ∈ Set.Icc 0 1) :
    M.parentEntrancePoint D e s ∈ segment ℝ
      (D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).enter))
      (D.boundaryPosition (C.boundaryTurn M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D e).enter))) := by
  rw [M.parentEntrancePoint_eq_lineMap D e s]
  exact lineMap_mem_segment ℝ _ _ inside

/-- All parameters in the unit interval lie on the actual exit bank segment. -/
theorem parentExitPoint_mem_segment
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) {s : ℝ} (inside : s ∈ Set.Icc 0 1) :
    M.parentExitPoint D e s ∈ segment ℝ
      (D.boundaryPosition (C.boundaryTurn M.retain
        (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)))
      (D.boundaryPosition (M.projectionContour.cycle.point (M.parentBankOpening D e).leave)) := by
  rw [M.parentExitPoint_eq_lineMap D e s]
  exact lineMap_mem_segment ℝ _ _ inside

end Unfoldings.ConvexCap.SectorForest
