module

public import Unfoldings.Cone.AppendFirst

/-!
# Continuing a cyclic metric map through its slit

A nonexpanding map of a slit angular fan whose two outer banks agree extends
over an appended copy of its first sector. The extension is constructed from
the cell maps and the actual bank equality. Radial distances remain exact.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) {Y : Type*}

def appendCellMap (f : A.Surface → Y) (i : Fin (n + 2)) : A.appendFirst.Cell i → Y := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact fun x => f (A.faceMap 0
      ⟨x.val, by simpa only [A.appendFirst_angle_last] using x.property⟩)
  · exact fun x => f (A.faceMap j
      ⟨x.val, by simpa only [A.appendFirst_angle_castSucc] using x.property⟩)

theorem appendCellMap_castSucc (f : A.Surface → Y) (i : Fin (n + 1))
    (x : A.appendFirst.Cell i.castSucc) :
    A.appendCellMap f i.castSucc x = f (A.faceMap i
      ⟨x.val, by simpa only [A.appendFirst_angle_castSucc] using x.property⟩) := by
  simp [appendCellMap]

theorem appendCellMap_last (f : A.Surface → Y)
    (x : A.appendFirst.Cell (Fin.last (n + 1))) :
    A.appendCellMap f (Fin.last (n + 1)) x = f (A.faceMap 0
      ⟨x.val, by simpa only [A.appendFirst_angle_last] using x.property⟩) := by
  simp [appendCellMap]

variable [EMetricSpace Y]

theorem appendCellMap_lipschitz (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (i : Fin (n + 2)) : LipschitzWith 1 (A.appendCellMap f i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro x y
    rw [A.appendCellMap_last, A.appendCellMap_last]
    have bound := nonexpanding.edist_le_mul
      (A.faceMap 0 ⟨x.val, by simpa only [A.appendFirst_angle_last] using x.property⟩)
      (A.faceMap 0 ⟨y.val, by simpa only [A.appendFirst_angle_last] using y.property⟩)
    rw [(A.faceMap_isometry 0).edist_eq] at bound
    exact bound
  · intro x y
    rw [A.appendCellMap_castSucc, A.appendCellMap_castSucc]
    have bound := nonexpanding.edist_le_mul
      (A.faceMap j ⟨x.val, by simpa only [A.appendFirst_angle_castSucc] using x.property⟩)
      (A.faceMap j ⟨y.val, by simpa only [A.appendFirst_angle_castSucc] using y.property⟩)
    rw [(A.faceMap_isometry j).edist_eq] at bound
    exact bound

omit [EMetricSpace Y] in
theorem appendCellMap_joined (f : A.Surface → Y)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) (i : Fin (n + 1)) (r : ℝ≥0) :
    A.appendCellMap f i.castSucc (A.appendFirst.finish i.castSucc r) =
      A.appendCellMap f i.succ (A.appendFirst.start i.succ r) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, A.appendCellMap_castSucc, A.appendCellMap_last]
    convert closes r using 1
    · apply congrArg f
      apply congrArg (A.faceMap (Fin.last n))
      apply Subtype.ext
      change (r : ℝ) • polarRay (A.appendFirst.angle (Fin.last n).castSucc) =
        (r : ℝ) • polarRay (A.angle (Fin.last n))
      rw [A.appendFirst_angle_castSucc]
    · apply congrArg f
      apply congrArg (A.faceMap 0)
      apply Subtype.ext
      rfl
  · rw [Fin.succ_castSucc, A.appendCellMap_castSucc, A.appendCellMap_castSucc]
    have joined : A.faceMap j.castSucc (A.finish j.castSucc r) =
        A.faceMap j.succ (A.start j.succ r) :=
      MetricGluing.point_eq_of_glue A.Cell ⟨j, r, rfl, rfl⟩
    convert congrArg f joined using 1
    · apply congrArg f
      apply congrArg (A.faceMap j.castSucc)
      apply Subtype.ext
      change (r : ℝ) • polarRay (A.appendFirst.angle j.castSucc.castSucc) =
        (r : ℝ) • polarRay (A.angle j.castSucc)
      rw [A.appendFirst_angle_castSucc]
    · apply congrArg f
      apply congrArg (A.faceMap j.succ)
      apply Subtype.ext
      rfl

omit [EMetricSpace Y] in
theorem appendCellMap_compatible (f : A.Surface → Y)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r)))
    (x y : MetricGluing.Total A.appendFirst.Cell) (joined : A.appendFirst.glue x y) :
    A.appendCellMap f x.1 x.2 = A.appendCellMap f y.1 y.2 := by
  obtain ⟨i, r, rfl, rfl⟩ := joined
  exact A.appendCellMap_joined f closes i r

def appendMap (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) : A.appendFirst.Surface → Y :=
  MetricGluing.lift A.appendFirst.Cell A.appendFirst.glue (A.appendCellMap f)
    (A.appendCellMap_lipschitz f nonexpanding) (A.appendCellMap_compatible f closes)

theorem appendMap_lipschitz (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) : LipschitzWith 1 (A.appendMap f nonexpanding closes) :=
  MetricGluing.lift_lipschitz A.appendFirst.Cell A.appendFirst.glue (A.appendCellMap f)
    (A.appendCellMap_lipschitz f nonexpanding) (A.appendCellMap_compatible f closes)

@[simp] theorem appendMap_faceMap (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) (i : Fin (n + 2)) (x : A.appendFirst.Cell i) :
    A.appendMap f nonexpanding closes (A.appendFirst.faceMap i x) = A.appendCellMap f i x := rfl

@[simp] theorem appendMap_original (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) (i : Fin (n + 1)) (x : A.Cell i) :
    A.appendMap f nonexpanding closes
      (A.appendFirst.faceMap i.castSucc (A.appendFirstCell i x)) = f (A.faceMap i x) := by
  rw [A.appendMap_faceMap, A.appendCellMap_castSucc]
  rfl

@[simp] theorem appendMap_extra (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) (x : A.Cell 0) :
    A.appendMap f nonexpanding closes
      (A.appendFirst.faceMap (Fin.last (n + 1)) (A.appendExtraCell x)) = f (A.faceMap 0 x) := by
  rw [A.appendMap_faceMap, A.appendCellMap_last]
  rfl

theorem appendMap_radial (f : A.Surface → Y) (nonexpanding : LipschitzWith 1 f)
    (closes : ∀ r : ℝ≥0, f (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      f (A.faceMap 0 (A.start 0 r))) (o : Y)
    (radial : ∀ x, edist o (f x) = edist A.origin x) (z : A.appendFirst.Surface) :
    edist o (A.appendMap f nonexpanding closes z) = edist A.appendFirst.origin z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.appendFirst.Cell A.appendFirst.glue z
  change edist o (A.appendMap f nonexpanding closes (A.appendFirst.faceMap i x)) =
    edist A.appendFirst.origin (A.appendFirst.faceMap i x)
  rw [A.appendMap_faceMap, A.appendFirst.edist_origin_faceMap]
  revert x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro x
    rw [A.appendCellMap_last, radial, A.edist_origin_faceMap]
  · intro x
    rw [A.appendCellMap_castSucc, radial, A.edist_origin_faceMap]

end Unfoldings.AngularFan
