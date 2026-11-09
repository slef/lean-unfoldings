module

public import Unfoldings.Complex.Exact

/-! Quantitative neighborhoods of nonvertex seam classes. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A directly paired nonvertex point has exactly its two tagged representatives. -/
theorem eqvGen_iff_eq_or_neighbor {retain : Set C.Seam} {a b c : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) :
    Relation.EqvGen (C.glue retain) a c ↔ c = a ∨ c = b := by
  rw [C.eqvGen_iff_of_regular retain regular]
  constructor
  · rintro (equal | crossed)
    · exact Or.inl equal.symm
    · exact Or.inr (C.crosses_unique regular crossing crossed).symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr crossing

theorem exists_class_transport (retain : Set C.Seam) (a : C.Total) :
    ∃ ε > 0, MetricGluing.ClassTransport C.Cell (C.glue retain) a ε := by
  have finite : ∀ i, (MetricGluing.classIn C.Cell (C.closedSeams retain).relation a i).Finite := by
    simpa only [C.closedSeams_relation] using C.finite_classIn retain a
  simpa only [C.closedSeams_relation] using (C.closedSeams retain).class_transport a finite

theorem classIn_eq_singleton_left {retain : Set C.Seam} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) (different : a.1 ≠ b.1) :
    MetricGluing.classIn C.Cell (C.glue retain) a a.1 = {a.2} := by
  ext x
  change Relation.EqvGen (C.glue retain) a ⟨a.1, x⟩ ↔ x = a.2
  constructor
  · intro related
    rcases (C.eqvGen_iff_eq_or_neighbor regular crossing).mp related with left | right
    · exact eq_of_heq (Sigma.mk.inj left).2
    · have faces := congrArg (fun p : C.Total => p.1) right
      exact (different faces).elim
  · rintro rfl
    exact Relation.EqvGen.refl a

theorem classIn_eq_singleton_right {retain : Set C.Seam} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) (different : a.1 ≠ b.1) :
    MetricGluing.classIn C.Cell (C.glue retain) a b.1 = {b.2} := by
  ext x
  change Relation.EqvGen (C.glue retain) a ⟨b.1, x⟩ ↔ x = b.2
  constructor
  · intro related
    rcases (C.eqvGen_iff_eq_or_neighbor regular crossing).mp related with left | right
    · have faces := congrArg (fun p : C.Total => p.1) left
      exact (different faces.symm).elim
    · exact eq_of_heq (Sigma.mk.inj right).2
  · rintro rfl
    exact (C.eqvGen_iff_eq_or_neighbor regular crossing).mpr (Or.inr rfl)

theorem classIn_eq_empty_of_ne {retain : Set C.Seam} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) {f : Face}
    (left : f ≠ a.1) (right : f ≠ b.1) : MetricGluing.classIn C.Cell (C.glue retain) a f = ∅ := by
  ext x
  change Relation.EqvGen (C.glue retain) a ⟨f, x⟩ ↔ False
  constructor
  · intro related
    rcases (C.eqvGen_iff_eq_or_neighbor regular crossing).mp related with equal | equal
    · exact left (congrArg (fun p : C.Total => p.1) equal)
    · exact right (congrArg (fun p : C.Total => p.1) equal)
  · exact False.elim

/-- A small metric neighborhood of a two-face seam class has no representatives in other faces. -/
theorem face_eq_or_of_near_class {retain : Set C.Seam} {a b c : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) {ε : ℝ} (positive : 0 < ε)
    (transport : MetricGluing.ClassTransport C.Cell (C.glue retain) a ε)
    (near : edist (MetricGluing.point C.Cell (C.glue retain) a)
      (MetricGluing.point C.Cell (C.glue retain) c) < ENNReal.ofReal ε) :
    c.1 = a.1 ∨ c.1 = b.1 := by
  by_contra neither
  have left : c.1 ≠ a.1 := fun h => neither (Or.inl h)
  have right : c.1 ≠ b.1 := fun h => neither (Or.inr h)
  have empty := C.classIn_eq_empty_of_ne regular crossing left right
  have value : MetricGluing.classBarrier C.Cell (C.glue retain) a ε c.1 c.2 = ε := by
    unfold MetricGluing.classBarrier
    rw [empty, MetricBarrier.cappedDist_empty]
  have lower := MetricGluing.classBarrier_le_edist C.Cell (C.glue retain) a positive.le
    (C.finite_classIn retain a) transport c
  rw [value] at lower
  exact (not_lt_of_ge lower) near

theorem dist_lt_of_near_left {retain : Set C.Seam} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) (different : a.1 ≠ b.1)
    {ε r : ℝ} (positive : 0 < ε) (small : r ≤ ε)
    (transport : MetricGluing.ClassTransport C.Cell (C.glue retain) a ε) (x : C.Cell a.1)
    (near : edist (MetricGluing.point C.Cell (C.glue retain) a) (C.faceMap retain a.1 x) <
      ENNReal.ofReal r) : dist x a.2 < r := by
  have lower := MetricGluing.classBarrier_le_edist C.Cell (C.glue retain) a positive.le
    (C.finite_classIn retain a) transport ⟨a.1, x⟩
  have value : MetricGluing.classBarrier C.Cell (C.glue retain) a ε a.1 x = min ε (dist x a.2) := by
    unfold MetricGluing.classBarrier
    rw [C.classIn_eq_singleton_left regular crossing different, MetricBarrier.cappedDist_singleton]
  rw [value] at lower
  have bound := lower.trans_lt near
  have less : min ε (dist x a.2) < r :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_min positive.le dist_nonneg)).mp bound
  exact (min_lt_iff.mp less).resolve_left (not_lt_of_ge small)

theorem dist_lt_of_near_right {retain : Set C.Seam} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (crossing : C.Crosses retain a b) (different : a.1 ≠ b.1)
    {ε r : ℝ} (positive : 0 < ε) (small : r ≤ ε)
    (transport : MetricGluing.ClassTransport C.Cell (C.glue retain) a ε) (x : C.Cell b.1)
    (near : edist (MetricGluing.point C.Cell (C.glue retain) a) (C.faceMap retain b.1 x) <
      ENNReal.ofReal r) : dist x b.2 < r := by
  have lower := MetricGluing.classBarrier_le_edist C.Cell (C.glue retain) a positive.le
    (C.finite_classIn retain a) transport ⟨b.1, x⟩
  have value : MetricGluing.classBarrier C.Cell (C.glue retain) a ε b.1 x = min ε (dist x b.2) := by
    unfold MetricGluing.classBarrier
    rw [C.classIn_eq_singleton_right regular crossing different, MetricBarrier.cappedDist_singleton]
  rw [value] at lower
  have bound := lower.trans_lt near
  have less : min ε (dist x b.2) < r :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_min positive.le dist_nonneg)).mp bound
  exact (min_lt_iff.mp less).resolve_left (not_lt_of_ge small)

end Unfoldings.TriangleComplex
