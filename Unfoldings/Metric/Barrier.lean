module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Capped distance barriers for metric gluing

Distance to an empty set is assigned the cap, rather than zero. This makes
barriers on different cells compatible when a seam class misses some cells.
Finite seam classes and local transport of nearby class points give exactness
of the route metric quotient.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricBarrier

open Metric

variable {X : Type*} [MetricSpace X]

/-- Distance to a set, capped at `ε`, with value `ε` for the empty set. -/
def cappedDist (ε : ℝ) (s : Set X) : X → ℝ := by
  classical
  exact if s.Nonempty then (fun x => min ε (infDist x s)) else fun _ => ε

@[simp] theorem cappedDist_empty (ε : ℝ) (x : X) : cappedDist ε ∅ x = ε := by
  simp [cappedDist]

@[simp] theorem cappedDist_singleton (ε : ℝ) (a x : X) :
    cappedDist ε {a} x = min ε (dist x a) := by simp [cappedDist, infDist_singleton]

theorem cappedDist_nonneg {ε : ℝ} (nonneg : 0 ≤ ε) (s : Set X) (x : X) :
    0 ≤ cappedDist ε s x := by
  classical
  unfold cappedDist
  split
  · exact le_min nonneg infDist_nonneg
  · exact nonneg

theorem cappedDist_of_mem {ε : ℝ} (nonneg : 0 ≤ ε) {s : Set X} {x : X} (inside : x ∈ s) :
    cappedDist ε s x = 0 := by
  simp [cappedDist, Set.nonempty_of_mem inside, infDist_zero_of_mem inside, min_eq_right nonneg]

theorem cappedDist_le (ε : ℝ) (s : Set X) (x : X) : cappedDist ε s x ≤ ε := by
  classical
  simp only [cappedDist]
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem cappedDist_le_dist (ε : ℝ) {s : Set X} {a : X} (ha : a ∈ s) (x : X) :
    cappedDist ε s x ≤ dist x a := by
  classical
  have bound : cappedDist ε s x ≤ infDist x s := by
    simp [cappedDist, Set.nonempty_of_mem ha]
  exact bound.trans (infDist_le_dist_of_mem ha)

/-- Being below the cap gives an actual nearby point of the set, even when it may be empty. -/
theorem exists_dist_lt_of_cappedDist_lt {ε r : ℝ} {s : Set X} {x : X}
    (small : r ≤ ε) (near : cappedDist ε s x < r) : ∃ y ∈ s, dist x y < r := by
  classical
  by_cases nonempty : s.Nonempty
  · have less : min ε (infDist x s) < r := by simpa [cappedDist, nonempty] using near
    exact (infDist_lt_iff nonempty).mp
      ((min_lt_iff.mp less).resolve_left (not_lt_of_ge small))
  · simp only [cappedDist, ite_eq_right nonempty] at near
    exact ((not_lt_of_ge small) near).elim

theorem cappedDist_lipschitz (ε : ℝ) (s : Set X) : LipschitzWith 1 (cappedDist ε s) := by
  classical
  by_cases nonempty : s.Nonempty
  · simpa [cappedDist, nonempty] using (lipschitz_infDist_pt s).const_min ε
  · simpa [cappedDist, nonempty] using
      (LipschitzWith.const ε : LipschitzWith 0 fun _ : X => ε).weaken zero_le_one

theorem cappedDist_eq_zero_iff {ε : ℝ} (positive : 0 < ε) {s : Set X} (closed : IsClosed s)
    (x : X) : cappedDist ε s x = 0 ↔ x ∈ s := by
  classical
  by_cases nonempty : s.Nonempty
  · simp only [cappedDist, ite_eq_left nonempty]
    rw [min_eq_iff]
    constructor
    · rintro (⟨impossible, _⟩ | ⟨zero, _⟩)
      · exact (positive.ne' impossible).elim
      · exact (closed.mem_iff_infDist_zero nonempty).mpr zero
    · intro hx
      exact Or.inr ⟨infDist_zero_of_mem hx, by rw [infDist_zero_of_mem hx]; exact positive.le⟩
  · simp [cappedDist, positive.ne', Set.not_nonempty_iff_eq_empty.mp nonempty]

/-- Transport of nearby class points is enough to compare their distance barriers. -/
theorem cappedDist_le_of_transport {Y : Type*} [MetricSpace Y] (ε : ℝ)
    {s : Set X} (finite : s.Finite) {t : Set Y} (x : X) (y : Y)
    (transport : ∀ a ∈ s, dist x a < ε → ∃ b ∈ t, dist y b ≤ dist x a) :
    cappedDist ε t y ≤ cappedDist ε s x := by
  classical
  by_cases nonempty : s.Nonempty
  · obtain ⟨a, ha, nearest⟩ := finite.isCompact.exists_infDist_eq_dist nonempty x
    by_cases near : dist x a < ε
    · obtain ⟨b, hb, bound⟩ := transport a ha near
      have value : cappedDist ε s x = dist x a := by
        simp [cappedDist, nonempty, nearest, min_eq_right near.le]
      rw [value]
      exact (cappedDist_le_dist ε hb y).trans bound
    · simpa [cappedDist, nonempty, nearest, min_eq_left (le_of_not_gt near)] using
        cappedDist_le ε t y
  · simpa [cappedDist, nonempty] using cappedDist_le ε t y

/-- A finite set has a uniform positive radius distinguishing membership in a closed set. -/
theorem exists_radius_near_closed {s t : Set X} (finite : s.Finite) (closed : IsClosed t) :
    ∃ ε > 0, ∀ x ∈ t, ∀ a ∈ s, dist x a < ε → a ∈ t := by
  classical
  induction s, finite using Set.Finite.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha finite ih =>
    obtain ⟨ε, positive, bound⟩ := ih
    by_cases inside : a ∈ t
    · refine ⟨ε, positive, ?_⟩
      intro x hx b hb near
      rcases hb with equal | hb
      · exact equal ▸ inside
      · exact bound x hx b hb near
    · obtain ⟨δ, δpos, ball⟩ := Metric.isOpen_iff.mp closed.isOpen_compl a inside
      refine ⟨min ε δ, lt_min positive δpos, ?_⟩
      intro x hx b hb near
      rcases hb with equal | hb
      · subst b
        have near' : dist x a < δ := near.trans_le (min_le_right ε δ)
        have outside : x ∉ t := ball (by simpa [Metric.mem_ball, dist_comm] using near')
        exact (outside hx).elim
      · exact bound x hx b hb (near.trans_le (min_le_left ε δ))

/-- Finitely many positive numbers have a common positive lower bound, even for an empty family. -/
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (r : ι → ℝ)
    (positive : ∀ i, 0 < r i) : ∃ ε > 0, ∀ i, ε ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ ε > 0, ∀ i ∈ s, ε ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, bound⟩ := ih
      refine ⟨min ε (r i), lt_min hε (positive i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (bound j hj)
  obtain ⟨ε, hε, bound⟩ := aux Finset.univ
  exact ⟨ε, hε, fun i => bound i (Finset.mem_univ i)⟩

end Unfoldings.MetricBarrier

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, MetricSpace (E i)]

/-- The points of a seam-equivalence class that lie in a specified original cell. -/
def classIn (glue : Total E → Total E → Prop) (a : Total E) (i : ι) : Set (E i) :=
  {x | Relation.EqvGen glue a ⟨i, x⟩}

/-- A local transport condition for class points near either side of a seam. -/
def ClassTransport (glue : Total E → Total E → Prop) (a : Total E) (ε : ℝ) : Prop :=
  ∀ x y, (glue x y ∨ glue y x) → ∀ z ∈ classIn E glue a x.1,
    dist x.2 z < ε → ∃ w ∈ classIn E glue a y.1, dist y.2 w ≤ dist x.2 z

/-- The capped distance to the copies of one seam class in each original cell. -/
def classBarrier (glue : Total E → Total E → Prop) (a : Total E) (ε : ℝ) (i : ι) : E i → ℝ :=
  MetricBarrier.cappedDist ε (classIn E glue a i)

theorem classBarrier_compatible (glue : Total E → Total E → Prop) (a : Total E) (ε : ℝ)
    (finite : ∀ i, (classIn E glue a i).Finite) (transport : ClassTransport E glue a ε) :
    ∀ x y, glue x y → classBarrier E glue a ε x.1 x.2 = classBarrier E glue a ε y.1 y.2 := by
  intro x y h
  apply le_antisymm
  · exact MetricBarrier.cappedDist_le_of_transport ε (finite y.1) y.2 x.2
      (transport y x (Or.inr h))
  · exact MetricBarrier.cappedDist_le_of_transport ε (finite x.1) x.2 y.2
      (transport x y (Or.inl h))

theorem classBarrier_center (glue : Total E → Total E → Prop) (a : Total E) {ε : ℝ}
    (nonneg : 0 ≤ ε) : classBarrier E glue a ε a.1 a.2 = 0 :=
  MetricBarrier.cappedDist_of_mem nonneg (Relation.EqvGen.refl a)

/-- Compatible class barriers are quantitative lower bounds for distance from the class. -/
theorem classBarrier_le_edist (glue : Total E → Total E → Prop) (a : Total E) {ε : ℝ}
    (nonneg : 0 ≤ ε) (finite : ∀ i, (classIn E glue a i).Finite)
    (transport : ClassTransport E glue a ε) (b : Total E) :
    ENNReal.ofReal (classBarrier E glue a ε b.1 b.2) ≤ edist (point E glue a) (point E glue b) := by
  change ENNReal.ofReal (classBarrier E glue a ε b.1 b.2) ≤ Route.distance (stepCost E glue) a b
  have bound := map_edist_le E glue (classBarrier E glue a ε)
    (fun i => MetricBarrier.cappedDist_lipschitz ε _)
    (classBarrier_compatible E glue a ε finite transport) a b
  rw [classBarrier_center E glue a nonneg] at bound
  have nonnegative : 0 ≤ classBarrier E glue a ε b.1 b.2 :=
    MetricBarrier.cappedDist_nonneg nonneg _ _
  simpa only [edist_dist, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg nonnegative] using bound

/-- A point close in the quotient has an original coordinate close to an actual class copy. -/
theorem exists_classPoint_of_edist_lt (glue : Total E → Total E → Prop) (a : Total E)
    {ε r : ℝ} (positive : 0 < ε) (small : r ≤ ε)
    (finite : ∀ i, (classIn E glue a i).Finite) (transport : ClassTransport E glue a ε)
    (b : Total E) (near : edist (point E glue a) (point E glue b) < ENNReal.ofReal r) :
    ∃ x ∈ classIn E glue a b.1, dist b.2 x < r := by
  have lower := classBarrier_le_edist E glue a positive.le finite transport b
  have nonnegative : 0 ≤ classBarrier E glue a ε b.1 b.2 :=
    MetricBarrier.cappedDist_nonneg positive.le _ _
  exact MetricBarrier.exists_dist_lt_of_cappedDist_lt small
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg nonnegative).mp (lower.trans_lt near))

/-- Finite classes with a positive local transport radius have no extra metric collapse. -/
theorem exact_of_finite_classes_of_transport (glue : Total E → Total E → Prop)
    (finite : ∀ a i, (classIn E glue a i).Finite)
    (transport : ∀ a, ∃ ε > 0, ClassTransport E glue a ε) : Exact E glue := by
  intro a b equal
  obtain ⟨ε, positive, radius⟩ := transport a
  let f : ∀ i, E i → ℝ := fun i => MetricBarrier.cappedDist ε (classIn E glue a i)
  have compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2 := by
    intro x y h
    apply le_antisymm
    · exact MetricBarrier.cappedDist_le_of_transport ε (finite a y.1) y.2 x.2
        (radius y x (Or.inr h))
    · exact MetricBarrier.cappedDist_le_of_transport ε (finite a x.1) x.2 y.2
        (radius x y (Or.inl h))
  have same : f a.1 a.2 = f b.1 b.2 :=
    congrArg (lift E glue f (fun i => MetricBarrier.cappedDist_lipschitz ε _) compatible) equal
  have zero : f a.1 a.2 = 0 :=
    (MetricBarrier.cappedDist_eq_zero_iff positive (finite a a.1).isClosed a.2).mpr
      (Relation.EqvGen.refl a)
  exact (MetricBarrier.cappedDist_eq_zero_iff positive (finite a b.1).isClosed b.2).mp
    (same.symm.trans zero)

end Unfoldings.MetricGluing
