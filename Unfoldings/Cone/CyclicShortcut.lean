module

public import Unfoldings.Cone.AppendMap
public import Unfoldings.Cone.CellShortcut

/-!
# Apex shortcuts through a cyclic closing seam

A radially exact nonexpanding map identifying the two outer banks of a fan
with total angle less than a full turn admits strict shortcuts between every
nonzero point in the first sector and every other nonzero point. If the
shorter arc crosses the slit, the appended first sector supplies its lift.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) {Y : Type*} [EMetricSpace Y]

theorem cyclic_first_cell_shortcut (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r)))
    (o : Y) (radial : ∀ z, edist o (f z) = edist A.origin z)
    (full_bound : A.totalAngle < 2 * Real.pi)
    (j : Fin (n + 1)) (x : A.Cell 0) (y : A.Cell j)
    (left_nonzero : x.val ≠ 0) (right_nonzero : y.val ≠ 0) :
    edist (f (A.faceMap 0 x)) (f (A.faceMap j y)) <
      edist (f (A.faceMap 0 x)) o + edist o (f (A.faceMap j y)) := by
  let B := A.appendFirst
  let F := A.appendMap f nonexpanding closes
  have lip : LipschitzWith 1 F := A.appendMap_lipschitz f nonexpanding closes
  have radial_F : ∀ z, edist o (F z) = edist B.origin z :=
    A.appendMap_radial f nonexpanding closes o radial
  obtain ⟨r, θ, θbounds, left_coordinates⟩ := A.exists_place_polar 0 x
  obtain ⟨s, φ, φbounds, right_coordinates⟩ := A.exists_place_polar j y
  have θnonneg : 0 ≤ θ := (A.heading_nonneg _).trans θbounds.1
  have θupper : θ ≤ A.angle 0 := by
    simpa only [A.heading_succ, Fin.castSucc_zero, A.heading_zero, zero_add] using θbounds.2
  have φnonneg : 0 ≤ φ := (A.heading_nonneg _).trans φbounds.1
  have φupper : φ ≤ A.totalAngle := φbounds.2.trans (A.heading_le_totalAngle _)
  have original_bounds (i : Fin (n + 1)) (t : ℝ)
      (bounds : t ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ)) :
      t ∈ Set.Icc (B.heading i.castSucc.castSucc) (B.heading i.castSucc.succ) := by
    simpa only [B, Fin.succ_castSucc, A.appendFirst_heading_castSucc] using bounds
  have original_coordinates :
      B.place j.castSucc (A.appendFirstCell j y) = (s : ℂ) * polarRay φ :=
    (A.appendFirst_place j y).trans right_coordinates
  by_cases close : |θ - φ| < Real.pi
  · have strict := B.nonexpanding_cell_shortcut F lip o radial_F
      (0 : Fin (n + 1)).castSucc j.castSucc (A.appendFirstCell 0 x) (A.appendFirstCell j y)
      r s θ φ (original_bounds 0 θ θbounds) (original_bounds j φ φbounds)
      ((A.appendFirst_place 0 x).trans left_coordinates) original_coordinates close
      left_nonzero right_nonzero
    simpa only [F, B, A.appendMap_original] using strict
  · have gap : Real.pi ≤ φ - θ := by
      by_contra no
      apply close
      apply abs_lt.mpr
      constructor <;> linarith [A.small 0]
    have extra_bounds : A.totalAngle + θ ∈
        Set.Icc (B.heading (Fin.last (n + 1)).castSucc)
          (B.heading (Fin.last (n + 1)).succ) := by
      dsimp only [B]
      rw [Fin.succ_last, A.appendFirst.heading_last,
        A.appendFirst_heading_extra, A.appendFirst_totalAngle]
      exact ⟨by linarith, by linarith⟩
    have extra_coordinates :
        B.place (Fin.last (n + 1)) (A.appendExtraCell x) =
          (r : ℂ) * polarRay (A.totalAngle + θ) := by
      rw [A.appendExtra_place]
      have local_coordinates : x.val = (r : ℂ) * polarRay θ := by
        simpa only [place, Fin.castSucc_zero, A.heading_zero, polarRay_zero, one_mul]
          using left_coordinates
      rw [local_coordinates, polarRay_add]
      ring
    have extra_close : |A.totalAngle + θ - φ| < Real.pi := by
      rw [abs_of_nonneg (by linarith : 0 ≤ A.totalAngle + θ - φ)]
      linarith
    have strict := B.nonexpanding_cell_shortcut F lip o radial_F
      (Fin.last (n + 1)) j.castSucc (A.appendExtraCell x) (A.appendFirstCell j y)
      r s (A.totalAngle + θ) φ extra_bounds (original_bounds j φ φbounds)
      extra_coordinates original_coordinates extra_close left_nonzero right_nonzero
    simpa only [F, B, A.appendMap_extra, A.appendMap_original] using strict

end Unfoldings.AngularFan
