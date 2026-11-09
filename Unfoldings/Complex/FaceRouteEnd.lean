module

public import Unfoldings.Complex.FaceRoutes

/-! The last genuine piece of an actual strictly ordered face route. -/

@[expose] public section

namespace Unfoldings.TriangleComplex.FaceRoute

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {a b : C.Realization Set.univ} {p : Path a b} (R : C.FaceRoute p)

theorem steps_pos : 0 < R.steps := by
  by_contra wrong
  have zero : R.steps = 0 := Nat.eq_zero_of_not_pos wrong
  have last_zero : Fin.last R.steps = 0 := Fin.ext zero
  have ends := R.finish
  rw [last_zero, R.start] at ends
  exact zero_ne_one ends

def lastIndex : Fin R.steps := ⟨R.steps - 1, by have positive := R.steps_pos; omega⟩

theorem lastIndex_succ : R.lastIndex.succ = Fin.last R.steps := by
  apply Fin.ext
  change R.steps - 1 + 1 = R.steps
  have positive := R.steps_pos
  omega

theorem last_end_time : R.time R.lastIndex.succ = 1 := by rw [R.lastIndex_succ, R.finish]

theorem last_entry_lt_one : R.time R.lastIndex.castSucc < 1 :=
  (R.increasing Fin.castSucc_lt_succ).trans_eq R.last_end_time

end Unfoldings.TriangleComplex.FaceRoute
