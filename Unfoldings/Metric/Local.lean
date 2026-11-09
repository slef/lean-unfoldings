module

public import Unfoldings.Metric.Barrier
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Tactic.Linarith

/-!
# Local isometry away from seams

A cell function that is constant on all seam attachment points extends by that
constant to the other cells. Capped distance functions then give quantitative
lower bounds on the gluing metric and isometric cell balls away from seams.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, MetricSpace (E i)]

/-- All points of a cell participating in any declared seam, in either orientation. -/
def seamSupport (glue : Total E → Total E → Prop) (i : ι) : Set (E i) :=
  {x | (∃ y, glue ⟨i, x⟩ y) ∨ ∃ y, glue y ⟨i, x⟩}

/-- Extend a single-cell function by a constant on every other cell. -/
def cellFunction {Y : Type*} (i : ι) (f : E i → Y) (c : Y) (j : ι) (x : E j) : Y := by
  classical
  exact if h : j = i then f (h ▸ x) else c

omit [∀ i, MetricSpace (E i)] in
@[simp] theorem cellFunction_self {Y : Type*} (i : ι) (f : E i → Y) (c : Y) (x : E i) :
    cellFunction E i f c i x = f x := by simp [cellFunction]

theorem cellFunction_lipschitz {Y : Type*} [EMetricSpace Y] (i : ι) (f : E i → Y) (c : Y)
    (nonexpanding : LipschitzWith 1 f) (j : ι) : LipschitzWith 1 (cellFunction E i f c j) := by
  classical
  by_cases equal : j = i
  · subst j
    have self : cellFunction E i f c i = f := funext (cellFunction_self E i f c)
    rw [self]
    exact nonexpanding
  · have constant : cellFunction E i f c j = fun _ => c := by
      funext x
      simp [cellFunction, equal]
    rw [constant]
    exact (LipschitzWith.const c).weaken zero_le_one

omit [∀ i, MetricSpace (E i)] in
theorem cellFunction_compatible {Y : Type*} (glue : Total E → Total E → Prop)
    (i : ι) (f : E i → Y) (c : Y)
    (on_support : ∀ x ∈ seamSupport E glue i, f x = c) :
    ∀ a b, glue a b → cellFunction E i f c a.1 a.2 = cellFunction E i f c b.1 b.2 := by
  classical
  have value (a : Total E) (touch : (∃ b, glue a b) ∨ ∃ b, glue b a) :
      cellFunction E i f c a.1 a.2 = c := by
    obtain ⟨j, x⟩ := a
    by_cases equal : j = i
    · subst j
      exact (cellFunction_self E i f c x).trans (on_support x touch)
    · simp [cellFunction, equal]
  intro a b h
  exact (value a (Or.inl ⟨b, h⟩)).trans (value b (Or.inr ⟨a, h⟩)).symm

/-- Distance capped at a seam-clearance radius is a lower bound on intrinsic distance. -/
theorem capped_dist_le_edist (glue : Total E → Total E → Prop) (i : ι) (p q : E i)
    {ε : ℝ} (nonneg : 0 ≤ ε)
    (clearance : ∀ x ∈ seamSupport E glue i, ε ≤ dist x p) :
    ENNReal.ofReal (min ε (dist q p)) ≤ edist (of E glue i p) (of E glue i q) := by
  change ENNReal.ofReal (min ε (dist q p)) ≤ Route.distance (stepCost E glue) ⟨i, p⟩ ⟨i, q⟩
  let f : E i → ℝ := fun x => min ε (dist x p)
  have nonexpanding : LipschitzWith 1 f := (LipschitzWith.dist_left p).const_min ε
  have compatible := cellFunction_compatible E glue i f ε
    (fun x hx => min_eq_left (clearance x hx))
  have bound := map_edist_le E glue (cellFunction E i f ε)
    (cellFunction_lipschitz E i f ε nonexpanding) compatible ⟨i, p⟩ ⟨i, q⟩
  simpa only [cellFunction_self, f, dist_self, min_eq_right nonneg, edist_dist,
    Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (le_min nonneg dist_nonneg)] using bound

/-- Other cells cannot be reached for less than the seam-clearance radius. -/
theorem clearance_le_edist_of_ne (glue : Total E → Total E → Prop) {i j : ι}
    (different : j ≠ i) (p : E i) (q : E j) {ε : ℝ} (nonneg : 0 ≤ ε)
    (clearance : ∀ x ∈ seamSupport E glue i, ε ≤ dist x p) :
    ENNReal.ofReal ε ≤ edist (of E glue i p) (of E glue j q) := by
  classical
  change ENNReal.ofReal ε ≤ Route.distance (stepCost E glue) ⟨i, p⟩ ⟨j, q⟩
  let f : E i → ℝ := fun x => min ε (dist x p)
  have nonexpanding : LipschitzWith 1 f := (LipschitzWith.dist_left p).const_min ε
  have compatible := cellFunction_compatible E glue i f ε
    (fun x hx => min_eq_left (clearance x hx))
  have bound := map_edist_le E glue (cellFunction E i f ε)
    (cellFunction_lipschitz E i f ε nonexpanding) compatible ⟨i, p⟩ ⟨j, q⟩
  have other : cellFunction E i f ε j q = ε := by simp [cellFunction, different]
  simpa only [cellFunction_self, other, f, dist_self, min_eq_right nonneg, edist_dist,
    Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg nonneg] using bound

/-- The ambient cell distance is preserved up to the first possible seam exit. -/
theorem edist_of_eq_of_clearance (glue : Total E → Total E → Prop) (i : ι) (p q : E i)
    {ε : ℝ} (nonneg : 0 ≤ ε)
    (clearance : ∀ x ∈ seamSupport E glue i, ε ≤ dist x p) (near : dist q p ≤ ε) :
    edist (of E glue i p) (of E glue i q) = edist p q := by
  apply le_antisymm (edist_of_le E glue i p q)
  have bound := capped_dist_le_edist E glue i p q nonneg clearance
  rw [min_eq_right near] at bound
  simpa only [edist_dist, dist_comm q p] using bound

/-- A ball with three times its radius clear of all attachments embeds isometrically. -/
theorem of_isometry_on_ball (glue : Total E → Total E → Prop) (i : ι) (p : E i)
    {r : ℝ} (nonneg : 0 ≤ r)
    (clearance : ∀ x ∈ seamSupport E glue i, 3 * r ≤ dist x p) :
    Isometry (fun x : Metric.ball p r => of E glue i x) := by
  intro x y
  apply edist_of_eq_of_clearance E glue i x y (ε := 2 * r) (mul_nonneg zero_le_two nonneg)
  · intro z hz
    have hx : dist x.val p < r := Metric.mem_ball.mp x.property
    have lower := clearance z hz
    have triangle := dist_triangle z x.val p
    linarith
  · have hx : dist x.val p < r := Metric.mem_ball.mp x.property
    have hy : dist y.val p < r := Metric.mem_ball.mp y.property
    have triangle := dist_triangle y.val p x.val
    rw [dist_comm p x.val] at triangle
    change dist y.val x.val ≤ 2 * r
    linarith

/-- A small metric ball has no representatives outside its original cell. -/
theorem eball_eq_image_ball (glue : Total E → Total E → Prop) (i : ι) (p : E i)
    {r ε : ℝ} (nonneg : 0 ≤ r) (small : r ≤ ε)
    (clearance : ∀ x ∈ seamSupport E glue i, ε ≤ dist x p) :
    Metric.eball (of E glue i p) (ENNReal.ofReal r) = of E glue i '' Metric.ball p r := by
  have εnonneg := nonneg.trans small
  ext z
  constructor
  · intro hz
    obtain ⟨⟨j, q⟩, rfl⟩ := point_surjective E glue z
    by_cases same : j = i
    · subst j
      rw [Metric.mem_eball, edist_comm] at hz
      change edist (of E glue i p) (of E glue i q) < ENNReal.ofReal r at hz
      have capped := (capped_dist_le_edist E glue i p q εnonneg clearance).trans_lt hz
      have near : min ε (dist q p) < r :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_min εnonneg dist_nonneg)).mp capped
      exact ⟨q, (min_lt_iff.mp near).resolve_left (not_lt_of_ge small), rfl⟩
    · rw [Metric.mem_eball, edist_comm] at hz
      change edist (of E glue i p) (of E glue j q) < ENNReal.ofReal r at hz
      have lower := clearance_le_edist_of_ne E glue same p q εnonneg clearance
      exact ((not_lt_of_ge ((ENNReal.ofReal_le_ofReal small).trans lower)) hz).elim
  · rintro ⟨q, hq, rfl⟩
    rw [Metric.mem_eball, edist_comm]
    exact (edist_of_le E glue i p q).trans_lt
      (edist_lt_ofReal.mpr (by simpa only [dist_comm] using Metric.mem_ball.mp hq))

/-- An intrinsic metric ball away from attachments is isometric to the original cell ball. -/
def ballIsometry (glue : Total E → Total E → Prop) (i : ι) (p : E i)
    {r : ℝ} (nonneg : 0 ≤ r)
    (clearance : ∀ x ∈ seamSupport E glue i, 3 * r ≤ dist x p) :
    Metric.ball p r ≃ᵢ Metric.eball (of E glue i p) (ENNReal.ofReal r) := by
  let f : Metric.ball p r → Metric.eball (of E glue i p) (ENNReal.ofReal r) := fun x =>
    ⟨of E glue i x, by
      rw [Metric.mem_eball, edist_comm]
      exact (edist_of_le E glue i p x).trans_lt
        (edist_lt_ofReal.mpr (by simpa only [dist_comm] using Metric.mem_ball.mp x.property))⟩
  have isometry : Isometry f := of_isometry_on_ball E glue i p nonneg clearance
  have surjective : Function.Surjective f := by
    intro z
    have image := (eball_eq_image_ball E glue i p nonneg (by linarith) clearance).le z.property
    obtain ⟨q, hq, equal⟩ := image
    exact ⟨⟨q, hq⟩, Subtype.ext equal⟩
  exact ⟨Equiv.ofBijective f ⟨isometry.injective, surjective⟩, isometry⟩

@[simp] theorem ballIsometry_apply (glue : Total E → Total E → Prop) (i : ι) (p : E i)
    {r : ℝ} (nonneg : 0 ≤ r)
    (clearance : ∀ x ∈ seamSupport E glue i, 3 * r ≤ dist x p) (x : Metric.ball p r) :
    (ballIsometry E glue i p nonneg clearance x).val = of E glue i x := rfl

end Unfoldings.MetricGluing
