module

public import Unfoldings.Metric.Barrier
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Exactness for finitely many closed isometric seams

The seam domains can be arbitrary metric spaces and the cells need not be
compact. Closed seam images and finite equivalence classes are sufficient to
prevent unintended zero-distance identifications. Finiteness of classes is a
genuine hypothesis: finitely many partial isometries can have infinite orbits.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w z

variable {ι : Type u} (E : ι → Type v) [∀ i, MetricSpace (E i)]

/-- Finitely many closed isometric identifications between metric cells. -/
structure ClosedSeams where
  Seam : Type w
  [finiteSeam : Finite Seam]
  Domain : Seam → Type z
  [metricDomain : ∀ s, MetricSpace (Domain s)]
  left : Seam → ι
  right : Seam → ι
  toLeft : ∀ s, Domain s → E (left s)
  toRight : ∀ s, Domain s → E (right s)
  left_isometry : ∀ s, Isometry (toLeft s)
  right_isometry : ∀ s, Isometry (toRight s)
  left_closed : ∀ s, IsClosed (Set.range (toLeft s))
  right_closed : ∀ s, IsClosed (Set.range (toRight s))

attribute [instance] ClosedSeams.finiteSeam ClosedSeams.metricDomain

namespace ClosedSeams

variable {E} (S : ClosedSeams.{u, v, w, z} E)

/-- The declared, oriented seam relation; the metric construction supplies the reverse. -/
def relation (a b : Total E) : Prop :=
  ∃ s, ∃ x : S.Domain s,
    a = ⟨S.left s, S.toLeft s x⟩ ∧ b = ⟨S.right s, S.toRight s x⟩

theorem class_transport (a : Total E)
    (finite : ∀ i, (classIn E S.relation a i).Finite) :
    ∃ ε > 0, ClassTransport E S.relation a ε := by
  classical
  have left_radius (s : S.Seam) := MetricBarrier.exists_radius_near_closed
    (finite (S.left s)) (S.left_closed s)
  have right_radius (s : S.Seam) := MetricBarrier.exists_radius_near_closed
    (finite (S.right s)) (S.right_closed s)
  choose l lpos lbound using left_radius
  choose r rpos rbound using right_radius
  obtain ⟨ε, positive, bound⟩ := MetricBarrier.exists_pos_le_of_finite
    (fun s => min (l s) (r s)) (fun s => lt_min (lpos s) (rpos s))
  refine ⟨ε, positive, ?_⟩
  intro x y related
  rcases related with forward | backward
  · obtain ⟨s, p, rfl, rfl⟩ := forward
    intro q hq near
    have on_seam : q ∈ Set.range (S.toLeft s) :=
      lbound s (S.toLeft s p) ⟨p, rfl⟩ q hq
        (near.trans_le ((bound s).trans (min_le_left _ _)))
    obtain ⟨t, rfl⟩ := on_seam
    refine ⟨S.toRight s t, ?_, ?_⟩
    · exact Relation.EqvGen.trans _ _ _ hq
        (Relation.EqvGen.rel _ _ ⟨s, t, rfl, rfl⟩)
    · exact le_of_eq ((S.right_isometry s).dist_eq p t |>.trans
        ((S.left_isometry s).dist_eq p t).symm)
  · obtain ⟨s, p, rfl, rfl⟩ := backward
    intro q hq near
    have on_seam : q ∈ Set.range (S.toRight s) :=
      rbound s (S.toRight s p) ⟨p, rfl⟩ q hq
        (near.trans_le ((bound s).trans (min_le_right _ _)))
    obtain ⟨t, rfl⟩ := on_seam
    refine ⟨S.toLeft s t, ?_, ?_⟩
    · exact Relation.EqvGen.trans _ _ _ hq
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨s, t, rfl, rfl⟩))
    · exact le_of_eq ((S.left_isometry s).dist_eq p t |>.trans
        ((S.right_isometry s).dist_eq p t).symm)

/-- Closed seams with finite classes give exactly the declared equivalence relation. -/
theorem exact_of_finite_classes
    (finite : ∀ a i, (classIn E S.relation a i).Finite) : Exact E S.relation :=
  exact_of_finite_classes_of_transport E S.relation finite
    (fun a => S.class_transport a (finite a))

end ClosedSeams
end Unfoldings.MetricGluing
