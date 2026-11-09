module

public import Unfoldings.Cone.HeadingShortcut
public import Unfoldings.Cone.HeadingInterval

/-!
# Shortcuts between specified original angular cells

Real headings less than pi apart select a common pointed sector. Its
isometric lift agrees with the specified original cell representatives,
including points on banks and coincident headings.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) {Y : Type*} [PseudoEMetricSpace Y]

theorem nonexpanding_cell_shortcut (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (o : Y) (radial : ∀ z, edist o (f z) = edist A.origin z)
    (i j : Fin (n + 1)) (x : A.Cell i) (y : A.Cell j)
    (r s : ℝ≥0) (θ φ : ℝ)
    (θbounds : θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ))
    (φbounds : φ ∈ Set.Icc (A.heading j.castSucc) (A.heading j.succ))
    (left_coordinates : A.place i x = (r : ℂ) * polarRay θ)
    (right_coordinates : A.place j y = (s : ℂ) * polarRay φ)
    (close : |θ - φ| < Real.pi) (left_nonzero : x.val ≠ 0) (right_nonzero : y.val ≠ 0) :
    edist (f (A.faceMap i x)) (f (A.faceMap j y)) <
      edist (f (A.faceMap i x)) o + edist o (f (A.faceMap j y)) := by
  obtain ⟨a, b, positive, small, first, last, θband, φband⟩ :=
    exists_pointed_heading_interval A.totalAngle A.totalAngle_pos θ φ
      ⟨(A.heading_nonneg _).trans θbounds.1,
        θbounds.2.trans (A.heading_le_totalAngle _)⟩
      ⟨(A.heading_nonneg _).trans φbounds.1,
        φbounds.2.trans (A.heading_le_totalAngle _)⟩ close
  have left_inside : A.place i x ∈ headingSector a b :=
    (mem_headingSector_iff_polar a b positive small _).mpr ⟨r, θ, θband, left_coordinates⟩
  have right_inside : A.place j y ∈ headingSector a b :=
    (mem_headingSector_iff_polar a b positive small _).mpr ⟨s, φ, φband, right_coordinates⟩
  let z : headingSector a b := ⟨A.place i x, left_inside⟩
  let w : headingSector a b := ⟨A.place j y, right_inside⟩
  have left_lift : A.headingLift a b positive small first last z = A.faceMap i x :=
    A.headingLift_place a b positive small first last i x left_inside
      ⟨θbounds.1.trans θband.2, θband.1.trans θbounds.2⟩
  have right_lift : A.headingLift a b positive small first last w = A.faceMap j y :=
    A.headingLift_place a b positive small first last j y right_inside
      ⟨φbounds.1.trans φband.2, φband.1.trans φbounds.2⟩
  have left_point_nonzero : z.val ≠ 0 :=
    mul_ne_zero (polarRay_ne_zero (A.heading i.castSucc)) left_nonzero
  have right_point_nonzero : w.val ≠ 0 :=
    mul_ne_zero (polarRay_ne_zero (A.heading j.castSucc)) right_nonzero
  have strict := A.nonexpanding_headingLift_shortcut f nonexpanding o radial a b
    positive small first last z w left_point_nonzero right_point_nonzero
  rw [left_lift, right_lift] at strict
  exact strict

end Unfoldings.AngularFan
