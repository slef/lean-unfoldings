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

end Unfoldings.MetricGluing.ClosedSeams
