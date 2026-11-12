module

public import Unfoldings.Geometry.FiveSectorFrameMargins
public import Unfoldings.Geometry.OrientedFramePhase

/-! Exact frame rotations and separation of nonadjacent comparison quadrants. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {t : ℝ} (positive : 0 < t) (small : t < 1)

/-- The local complex coordinate of a vector in the sector's oriented frame. -/
def fiveSectorComplexFrame (k : Fin 5) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.trans
    (fiveSectorFrame t positive small (fiveSectorCycle k)).place

theorem fiveSectorComplexFrame_eq_rotation (k : Fin 5) (z : ℂ) :
    fiveSectorComplexFrame positive small k z =
      polarRay (-((fiveSectorComplexRay t 0).arg +
        fiveSectorQuadrantStart positive small k)) * z := by
  let B := fiveSectorFrame t positive small (fiveSectorCycle k)
  have nonzero : fiveSectorComplexRay t k ≠ 0 := by
    intro zero
    have original := congrArg Complex.orthonormalBasisOneI.repr zero
    simp only [fiveSectorComplexRay, LinearIsometryEquiv.apply_symm_apply, map_zero] at original
    exact B.first_ne original
  have mapped : fiveSectorComplexFrame positive small k (fiveSectorComplexRay t k) =
      (‖fiveSectorComplexRay t k‖ : ℂ) * polarRay B.margin := by
    simpa only [fiveSectorComplexFrame, fiveSectorComplexRay, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using B.first
  have formula := oriented_frame_eq_polarRay_mul (fiveSectorComplexFrame positive small k)
    (fiveSectorFrame_commutes_mul t positive small (fiveSectorCycle k)) nonzero
    (fiveSectorComplexRay_heading positive small k) mapped z
  convert formula using 2
  congr 1
  dsimp only [fiveSectorQuadrantStart, B]
  ring

theorem fiveSectorComplexFrame_change (i j : Fin 5) (z : ℂ) :
    fiveSectorComplexFrame positive small i z =
      polarRay (fiveSectorQuadrantStart positive small j -
        fiveSectorQuadrantStart positive small i) *
          fiveSectorComplexFrame positive small j z := by
  rw [fiveSectorComplexFrame_eq_rotation positive small,
    fiveSectorComplexFrame_eq_rotation positive small,
    ← mul_assoc, ← polarRay_add]
  congr 2
  ring

/-- Open quadrants of nonadjacent sectors are disjoint in the common plane. -/
theorem fiveSectorComplexFrame_quadrants_disjoint_of_gap (i j : Fin 5)
    (large : Real.pi / 2 ≤ fiveSectorQuadrantStart positive small j -
      fiveSectorQuadrantStart positive small i)
    (small_gap : fiveSectorQuadrantStart positive small j -
      fiveSectorQuadrantStart positive small i < Real.pi) :
    Disjoint {z : ℂ | 0 < (fiveSectorComplexFrame positive small i z).re ∧
        0 < (fiveSectorComplexFrame positive small i z).im}
      {z : ℂ | 0 < (fiveSectorComplexFrame positive small j z).re ∧
        0 < (fiveSectorComplexFrame positive small j z).im} := by
  apply Set.disjoint_left.mpr
  intro z first last
  exact not_both_quadrants_of_rotation large small_gap
    (fiveSectorComplexFrame_change positive small i j z) first.1 ⟨last.1.le, last.2⟩

theorem fiveSectorComplexFrame_quadrants_disjoint_two_apart (k : Fin 3) :
    Disjoint {z : ℂ | 0 < (fiveSectorComplexFrame positive small k.castSucc.castSucc z).re ∧
        0 < (fiveSectorComplexFrame positive small k.castSucc.castSucc z).im}
      {z : ℂ | 0 < (fiveSectorComplexFrame positive small k.succ.succ z).re ∧
        0 < (fiveSectorComplexFrame positive small k.succ.succ z).im} :=
  fiveSectorComplexFrame_quadrants_disjoint_of_gap positive small _ _
    (fiveSectorQuadrantStart_two_apart positive small k).1.le
    (fiveSectorQuadrantStart_two_apart positive small k).2

theorem fiveSectorComplexFrame_quadrants_disjoint_of_wrapped_gap (i j : Fin 5)
    (large : Real.pi / 2 ≤ fiveSectorQuadrantStart positive small j + 2 * Real.pi -
      fiveSectorQuadrantStart positive small i)
    (small_gap : fiveSectorQuadrantStart positive small j + 2 * Real.pi -
      fiveSectorQuadrantStart positive small i < Real.pi) :
    Disjoint {z : ℂ | 0 < (fiveSectorComplexFrame positive small i z).re ∧
        0 < (fiveSectorComplexFrame positive small i z).im}
      {z : ℂ | 0 < (fiveSectorComplexFrame positive small j z).re ∧
        0 < (fiveSectorComplexFrame positive small j z).im} := by
  apply Set.disjoint_left.mpr
  intro z first last
  have rotation := fiveSectorComplexFrame_change positive small i j z
  have periodic : polarRay (fiveSectorQuadrantStart positive small j + 2 * Real.pi -
      fiveSectorQuadrantStart positive small i) =
      polarRay (fiveSectorQuadrantStart positive small j -
        fiveSectorQuadrantStart positive small i) := by
    rw [show fiveSectorQuadrantStart positive small j + 2 * Real.pi -
        fiveSectorQuadrantStart positive small i =
        (fiveSectorQuadrantStart positive small j - fiveSectorQuadrantStart positive small i) +
          2 * Real.pi by ring]
    exact congrArg (fun x : Circle => (x : ℂ)) (Circle.exp_add_two_pi _)
  rw [← periodic] at rotation
  exact not_both_quadrants_of_rotation large small_gap rotation first.1 ⟨last.1.le, last.2⟩

/-- All nonadjacent pairs, including both pairs crossing the chosen angle seam. -/
theorem fiveSectorComplexFrame_quadrants_disjoint_nonadjacent (i j : Fin 5)
    (different : i ≠ j) (not_next : finRotate 5 i ≠ j) (not_previous : finRotate 5 j ≠ i) :
    Disjoint {z : ℂ | 0 < (fiveSectorComplexFrame positive small i z).re ∧
        0 < (fiveSectorComplexFrame positive small i z).im}
      {z : ℂ | 0 < (fiveSectorComplexFrame positive small j z).re ∧
        0 < (fiveSectorComplexFrame positive small j z).im} := by
  have first_wrap := fiveSectorQuadrantStart_wrap_two_apart positive small
  have wrap30 := fiveSectorComplexFrame_quadrants_disjoint_of_wrapped_gap positive small 3 0
    first_wrap.1.1.le first_wrap.1.2
  have wrap41 := fiveSectorComplexFrame_quadrants_disjoint_of_wrapped_gap positive small 4 1
    first_wrap.2.1.le first_wrap.2.2
  have pair02 := fiveSectorComplexFrame_quadrants_disjoint_two_apart positive small (0 : Fin 3)
  have pair13 := fiveSectorComplexFrame_quadrants_disjoint_two_apart positive small (1 : Fin 3)
  have pair24 := fiveSectorComplexFrame_quadrants_disjoint_two_apart positive small (2 : Fin 3)
  fin_cases i <;> fin_cases j <;>
    first
    | exact (different rfl).elim
    | exact (not_next rfl).elim
    | exact (not_previous rfl).elim
    | exact pair02
    | exact pair02.symm
    | exact pair13
    | exact pair13.symm
    | exact pair24
    | exact pair24.symm
    | exact wrap30
    | exact wrap30.symm
    | exact wrap41
    | exact wrap41.symm

end Unfoldings
