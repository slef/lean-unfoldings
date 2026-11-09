module

public import Unfoldings.Cone.SectorCoordinates
public import Unfoldings.Metric.Quotient
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Order.Fin.Basic

/-!
# Slit angular fans with constructed metrics and developments

Each piece is an actual closed Euclidean sector of angle strictly between
zero and pi. Glue each terminal ray to the next initial ray at equal radius.
Cumulative real headings give a planar development for every total angle,
including developments that overlap.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings

/-- A nonempty finite list of genuine convex sector angles. -/
structure AngularFan (n : ℕ) where
  angle : Fin (n + 1) → ℝ
  positive : ∀ i, 0 < angle i
  small : ∀ i, angle i < Real.pi

namespace AngularFan

variable {n : ℕ} (A : AngularFan n)

/-- Headings keep every full turn rather than reducing modulo a period. -/
def heading : Fin (n + 2) → ℝ := Fin.partialSum A.angle

@[simp] theorem heading_zero : A.heading 0 = 0 := Fin.partialSum_zero A.angle

theorem heading_succ (i : Fin (n + 1)) :
    A.heading i.succ = A.heading i.castSucc + A.angle i :=
  Fin.partialSum_succ A.angle i

theorem heading_strictMono : StrictMono A.heading := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [A.heading_succ]
  exact lt_add_of_pos_right _ (A.positive i)

def totalAngle : ℝ := ∑ i, A.angle i

theorem heading_last : A.heading (Fin.last (n + 1)) = A.totalAngle := by
  change ((List.ofFn A.angle).take (n + 1)).sum = ∑ i, A.angle i
  rw [List.take_of_length_le (by simp)]
  exact List.sum_ofFn

theorem totalAngle_pos : 0 < A.totalAngle :=
  Finset.sum_pos (fun i _ => A.positive i) Finset.univ_nonempty

abbrev Cell (i : Fin (n + 1)) : Type := planarSector (A.angle i)

def start (i : Fin (n + 1)) (r : ℝ≥0) : A.Cell i :=
  ⟨(r : ℂ), (r : ℝ), r.coe_nonneg, 0, le_rfl, by simp⟩

def finish (i : Fin (n + 1)) (r : ℝ≥0) : A.Cell i :=
  ⟨(r : ℝ) • polarRay (A.angle i), 0, le_rfl, (r : ℝ), r.coe_nonneg, by simp⟩

@[simp] theorem finish_zero (i : Fin (n + 1)) : A.finish i 0 = A.start i 0 := by
  apply Subtype.ext
  simp [finish, start]

/-- The two outer banks stay distinct; only consecutive internal rays are identified. -/
def glue (a b : MetricGluing.Total A.Cell) : Prop :=
  ∃ i : Fin n, ∃ r : ℝ≥0,
    a = ⟨i.castSucc, A.finish i.castSucc r⟩ ∧ b = ⟨i.succ, A.start i.succ r⟩

abbrev Surface := MetricGluing.Realization A.Cell A.glue

def faceMap (i : Fin (n + 1)) : A.Cell i → A.Surface := MetricGluing.of A.Cell A.glue i

theorem faceMap_lipschitz (i : Fin (n + 1)) : LipschitzWith 1 (A.faceMap i) :=
  MetricGluing.of_lipschitz A.Cell A.glue i

/-- The actual rotated planar sector coordinates of each piece. -/
def place (i : Fin (n + 1)) (x : A.Cell i) : ℂ :=
  polarRay (A.heading i.castSucc) * x.val

theorem place_isometry (i : Fin (n + 1)) : Isometry (A.place i) := by
  change Isometry (rotation (Circle.exp (A.heading i.castSucc)) ∘
    (Subtype.val : A.Cell i → ℂ))
  exact (rotation _).isometry.comp isometry_subtype_coe

theorem place_joined (i : Fin n) (r : ℝ≥0) :
    A.place i.castSucc (A.finish i.castSucc r) = A.place i.succ (A.start i.succ r) := by
  have next_heading : A.heading i.succ.castSucc =
      A.heading i.castSucc.castSucc + A.angle i.castSucc := by
    simpa only [Fin.succ_castSucc] using A.heading_succ i.castSucc
  change polarRay (A.heading i.castSucc.castSucc) *
    ((r : ℝ) • polarRay (A.angle i.castSucc)) =
      polarRay (A.heading i.succ.castSucc) * (r : ℂ)
  rw [next_heading, polarRay_add]
  simp only [Complex.real_smul]
  ring

theorem place_compatible (a b : MetricGluing.Total A.Cell) (joined : A.glue a b) :
    A.place a.1 a.2 = A.place b.1 b.2 := by
  obtain ⟨i, r, rfl, rfl⟩ := joined
  exact A.place_joined i r

/-- A planar development exists at every angular width; injectivity is a separate question. -/
def develop : A.Surface → ℂ :=
  MetricGluing.lift A.Cell A.glue A.place (fun i => (A.place_isometry i).lipschitzWith)
    A.place_compatible

@[simp] theorem develop_faceMap (i : Fin (n + 1)) (x : A.Cell i) :
    A.develop (A.faceMap i x) = A.place i x := rfl

theorem develop_lipschitz : LipschitzWith 1 A.develop :=
  MetricGluing.lift_lipschitz A.Cell A.glue A.place
    (fun i => (A.place_isometry i).lipschitzWith) A.place_compatible

/-- Since each piece is rigidly placed, the constructed intrinsic face maps are isometric. -/
theorem faceMap_isometry (i : Fin (n + 1)) : Isometry (A.faceMap i) := by
  intro x y
  apply le_antisymm
  · exact MetricGluing.edist_of_le A.Cell A.glue i x y
  · have lower := A.develop_lipschitz.edist_le_mul (A.faceMap i x) (A.faceMap i y)
    simp only [ENNReal.coe_one, one_mul, A.develop_faceMap] at lower
    exact (A.place_isometry i x y).symm.le.trans lower

end AngularFan
end Unfoldings
