module

public import Unfoldings.Metric.ClosedSeams
public import Unfoldings.Metric.LocalMap

/-!
# Local development estimates for closed seams

A family of nonexpanding cell maps need only agree across seams incident to
the chosen equivalence class. Finitely many closed seams and finite classes
then give a neighborhood where every route step is nonexpanding.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

universe u v w z

variable {ι : Type u} {E : ι → Type v} [∀ i, MetricSpace (E i)]
  (S : ClosedSeams.{u, v, w, z} E) {Y : Type*} [PseudoEMetricSpace Y]

/-- Seams incident to a class are those whose left image contains a copy of it. -/
def Incident (a : Total E) (s : S.Seam) : Prop :=
  ∃ x ∈ classIn E S.relation a (S.left s), x ∈ Set.range (S.toLeft s)

omit [PseudoEMetricSpace Y] in
/-- Compatibility at incident seams already makes a map constant on the chosen class. -/
theorem class_eq_of_incident_compatible (a : Total E) (f : ∀ i, E i → Y)
    (compatible : ∀ s, S.Incident a s → ∀ x, f (S.left s) (S.toLeft s x) =
      f (S.right s) (S.toRight s x)) {b : Total E}
    (related : Relation.EqvGen S.relation a b) : f a.1 a.2 = f b.1 b.2 := by
  have invariant {x y : Total E} (h : Relation.EqvGen S.relation x y) :
      Relation.EqvGen S.relation a x → f x.1 x.2 = f y.1 y.2 := by
    induction h with
    | rel x y h =>
      obtain ⟨s, p, rfl, rfl⟩ := h
      intro reaches
      exact compatible s ⟨_, reaches, p, rfl⟩ p
    | refl x => exact fun _ => rfl
    | symm x y h ih =>
      intro reaches
      exact (ih (Relation.EqvGen.trans _ _ _ reaches (Relation.EqvGen.symm _ _ h))).symm
    | trans x y z hxy hyz ih₁ ih₂ =>
      intro reaches
      exact (ih₁ reaches).trans (ih₂ (Relation.EqvGen.trans _ _ _ reaches hxy))
  exact invariant related (Relation.EqvGen.refl _)

/-- Compatibility at incident seams suffices for a local route-step estimate. -/
theorem exists_radius_local_step (a : Total E)
    (finite : ∀ i, (classIn E S.relation a i).Finite) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ s, S.Incident a s → ∀ x, f (S.left s) (S.toLeft s x) =
      f (S.right s) (S.toRight s x)) :
    ∃ r > 0, ∀ b c,
      edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r →
      edist (point E S.relation a) (point E S.relation c) < ENNReal.ofReal r →
      edist (f b.1 b.2) (f c.1 c.2) ≤ stepCost E S.relation b c := by
  classical
  obtain ⟨ε, positive, transport⟩ := S.class_transport a finite
  have radii (s : S.Seam) := MetricBarrier.exists_radius_near_closed
    (finite (S.left s)) (S.left_closed s)
  choose δ δpos δbound using radii
  obtain ⟨η, ηpos, ηbound⟩ := MetricBarrier.exists_pos_le_of_finite δ δpos
  let r := min ε η
  have rpos : 0 < r := lt_min positive ηpos
  have local_compatible (b c : Total E)
      (near : edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r)
      (joined : S.relation b c) : f b.1 b.2 = f c.1 c.2 := by
    obtain ⟨s, x, rfl, rfl⟩ := joined
    obtain ⟨q, hq, close⟩ := exists_classPoint_of_edist_lt E S.relation a positive
      (min_le_left ε η) finite transport _ near
    have member : q ∈ Set.range (S.toLeft s) :=
      δbound s (S.toLeft s x) ⟨x, rfl⟩ q hq
        (close.trans_le ((min_le_right ε η).trans (ηbound s)))
    exact compatible s ⟨q, hq, member⟩ x
  refine ⟨r, rpos, ?_⟩
  intro b c hb hc
  by_cases joined : S.relation b c ∨ S.relation c b
  · have equal : f b.1 b.2 = f c.1 c.2 := joined.elim
      (local_compatible b c hb) (fun h => (local_compatible c b hc h).symm)
    simp [stepCost, joined, equal]
  · obtain ⟨i, b⟩ := b
    obtain ⟨j, c⟩ := c
    by_cases same : i = j
    · subst j
      simpa [stepCost, joined, faceCost] using (nonexpanding i).edist_le_mul b c
    · simp [stepCost, joined, faceCost, same]

/-- Incident compatibility suffices for a local metric bound, without global descent. -/
theorem exists_radius_map_edist_le (a : Total E)
    (finite : ∀ i, (classIn E S.relation a i).Finite) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ s, S.Incident a s → ∀ x, f (S.left s) (S.toLeft s x) =
      f (S.right s) (S.toRight s x)) : ∃ r > 0, ∀ b c,
      edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r →
      edist (point E S.relation a) (point E S.relation c) < ENNReal.ofReal r →
      edist (f b.1 b.2) (f c.1 c.2) ≤ edist (point E S.relation b) (point E S.relation c) := by
  obtain ⟨δ, δpos, step⟩ := S.exists_radius_local_step a finite f nonexpanding compatible
  obtain ⟨ε, εpos, transport⟩ := S.class_transport a finite
  let r := min ε (δ / 3)
  have positive : 0 < r := lt_min εpos (div_pos δpos (by norm_num))
  have small : r ≤ ε := min_le_left _ _
  have budget_radius : 3 * r ≤ δ := by
    have bound : r ≤ δ / 3 := min_le_right _ _
    linarith
  have radial (b : Total E)
      (near : edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r) :
      edist (f a.1 a.2) (f b.1 b.2) < ENNReal.ofReal r := by
    obtain ⟨q, related, close⟩ := exists_classPoint_of_edist_lt E S.relation a εpos small
      finite transport b near
    have equal := S.class_eq_of_incident_compatible a f compatible related
    have bound := (nonexpanding b.1).edist_le_mul q b.2
    simp only [ENNReal.coe_one, one_mul] at bound
    rw [equal]
    apply bound.trans_lt
    rw [edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr close
  refine ⟨r, positive, ?_⟩
  intro b c hb hc
  have left : edist (f b.1 b.2) (f a.1 a.2) < ENNReal.ofReal r := by
    rw [edist_comm]
    exact radial b hb
  have chord := (edist_triangle (f b.1 b.2) (f a.1 a.2) (f c.1 c.2)).trans_lt
    (ENNReal.add_lt_add left (radial c hc))
  have total := ENNReal.add_lt_add hb chord
  have radius_sum : ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) =
      ENNReal.ofReal (3 * r) := by
    rw [← ENNReal.ofReal_add positive.le positive.le,
      ← ENNReal.ofReal_add positive.le (add_nonneg positive.le positive.le)]
    congr 1
    ring
  rw [radius_sum] at total
  exact map_edist_le_edist_of_budget E S.relation (fun x => f x.1 x.2) _
    (ENNReal.ofReal δ) step b c (total.trans_le (ENNReal.ofReal_le_ofReal budget_radius))

end Unfoldings.MetricGluing.ClosedSeams
