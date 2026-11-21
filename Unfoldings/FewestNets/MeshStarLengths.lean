module

public import Unfoldings.FewestNets.CheckedMeshStar
public import Unfoldings.FewestNets.CountConstants

/-! Algebraic bounds on the lengths of the dual sides of a site star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

variable {n : ℕ} (star : MeshStar (n + 1))

/-- Chord of the proposed dual side, joining successive circumcenters. -/
def dualChord (i : Fin (n + 1)) : ℝ := ‖star.dualDirection (i + 1) - star.dualDirection i‖

/-- Upper bound on the side angle from its chord. -/
def dualArcUpper (i : Fin (n + 1)) : ℝ :=
  star.dualChord i / Real.sqrt (1 - star.dualChord i ^ 2 / 4)

namespace Checked

open CheckedReal CheckedSpace

variable {D : ℕ} (hD : 0 < D) {star} (a : Checked D star)

def dualChord (i : Fin (n + 1)) : CheckedReal D (star.dualChord i) :=
  CheckedSpace.norm hD (CheckedSpace.sub (a.dualDirection hD (i + 1)) (a.dualDirection hD i))

def dualArcUpper (i : Fin (n + 1)) : CheckedReal D (star.dualArcUpper i) :=
  let c := a.dualChord hD i
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  let four : CheckedReal D (4 : ℝ) := (rat D 4).convert (by simp)
  c.div hD ((one.sub ((c.square hD).div hD four)).sqrt hD)

def checkIcosahedronEdge : CheckedReal D icosahedronEdge :=
  (rat D 4).div hD (((rat D 10).add ((rat D 2).mul hD ((rat D 5).sqrt hD))).sqrt hD) |>.convert
    (by simp [icosahedronEdge])

def checkTwiceStep (q : ℕ) : CheckedReal D (2 * (icosahedronEdge / q)) :=
  ((rat D 2).mul hD ((checkIcosahedronEdge hD).div hD (checkNat D q))).convert
    (by simp)

/-- Check both the choice of outward direction and the local dual-side length. -/
def checkDualSide (i : Fin (n + 1)) (q : ℕ) : Bool :=
  (a.dualOffset hD i).isPositive && (a.dualArcUpper hD i).isLT (checkTwiceStep hD q)

theorem dualSide_of_check {i : Fin (n + 1)} {q : ℕ} (h : a.checkDualSide hD i q = true) :
    0 < inner ℝ star.direction (star.dual i) ∧
      star.dualArcUpper i < 2 * (icosahedronEdge / q) := by
  rw [checkDualSide, Bool.and_eq_true] at h
  exact ⟨positive_of_isPositive hD _ h.1, lt_of_isLT hD _ _ h.2⟩

/-- Check every dual offset and side bound around the star. -/
def checkStar (q : ℕ) : Bool :=
  (List.finRange (n + 1)).all fun i => a.checkDualSide hD i q

theorem allDualSides_of_check {q : ℕ} (h : a.checkStar hD q = true) (i : Fin (n + 1)) :
    0 < inner ℝ star.direction (star.dual i) ∧
      star.dualArcUpper i < 2 * (icosahedronEdge / q) := by
  exact a.dualSide_of_check hD (List.all_eq_true.mp h i (List.mem_finRange i))

end Checked
end Unfoldings.FewestNets.MeshStar
