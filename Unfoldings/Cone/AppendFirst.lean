module

public import Unfoldings.Cone.AngularMetric

/-!
# Extending an angular fan across its last bank

Append a second copy of the first sector. For a cyclic fan, this extra piece
will continue the angular walk across the chosen slit. All headings remain
real, so the additional copy retains its correct sheet even if the extended
development overlaps.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

def appendFirst : AngularFan (n + 1) where
  angle := Fin.lastCases (A.angle 0) A.angle
  positive i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using A.positive 0
    · simpa using A.positive j
  small i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using A.small 0
    · simpa using A.small j

@[simp] theorem appendFirst_angle_castSucc (i : Fin (n + 1)) :
    A.appendFirst.angle i.castSucc = A.angle i := by simp [appendFirst]

@[simp] theorem appendFirst_angle_last :
    A.appendFirst.angle (Fin.last (n + 1)) = A.angle 0 := by simp [appendFirst]

theorem appendFirst_heading_castSucc (i : Fin (n + 2)) :
    A.appendFirst.heading i.castSucc = A.heading i := by
  induction i using Fin.inductionOn with
  | zero => simp
  | succ i ih =>
    rw [← Fin.succ_castSucc, A.appendFirst.heading_succ, A.heading_succ,
      A.appendFirst_angle_castSucc, ih]

theorem appendFirst_heading_extra :
    A.appendFirst.heading (Fin.last (n + 1)).castSucc = A.totalAngle := by
  rw [A.appendFirst_heading_castSucc, A.heading_last]

theorem appendFirst_totalAngle :
    A.appendFirst.totalAngle = A.totalAngle + A.angle 0 := by
  rw [← A.appendFirst.heading_last, ← Fin.succ_last, A.appendFirst.heading_succ,
    A.appendFirst_heading_extra, A.appendFirst_angle_last]

/-- Original cells, with unchanged Euclidean coordinates. -/
def appendFirstCell (i : Fin (n + 1)) (x : A.Cell i) : A.appendFirst.Cell i.castSucc :=
  ⟨x.val, by simpa only [A.appendFirst_angle_castSucc] using x.property⟩

/-- The extra copy of the first cell, with unchanged Euclidean coordinates. -/
def appendExtraCell (x : A.Cell 0) : A.appendFirst.Cell (Fin.last (n + 1)) :=
  ⟨x.val, by simpa only [A.appendFirst_angle_last] using x.property⟩

@[simp] theorem appendFirstCell_val (i : Fin (n + 1)) (x : A.Cell i) :
    (A.appendFirstCell i x).val = x.val := rfl

@[simp] theorem appendExtraCell_val (x : A.Cell 0) : (A.appendExtraCell x).val = x.val := rfl

theorem appendFirst_place (i : Fin (n + 1)) (x : A.Cell i) :
    A.appendFirst.place i.castSucc (A.appendFirstCell i x) = A.place i x := by
  change polarRay (A.appendFirst.heading i.castSucc.castSucc) * x.val =
    polarRay (A.heading i.castSucc) * x.val
  rw [A.appendFirst_heading_castSucc]

theorem appendExtra_place (x : A.Cell 0) :
    A.appendFirst.place (Fin.last (n + 1)) (A.appendExtraCell x) =
      polarRay A.totalAngle * x.val := by
  change polarRay (A.appendFirst.heading (Fin.last (n + 1)).castSucc) * x.val = _
  rw [A.appendFirst_heading_extra]

end Unfoldings.AngularFan
