module

public import Unfoldings.Complex.Exact
public import Unfoldings.Metric.Excision

/-! Cutting seams away from a point class preserves its small whole intrinsic balls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A seam is incident when its left edge contains a copy of the chosen point class. -/
def SeamIncident (retain : Set C.Seam) (a : C.Total) (s : C.Seam) : Prop :=
  ∃ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    Relation.EqvGen (C.glue retain) a (C.edgePoint (C.left s) x)

theorem seamIncident_of_closedSeams_incident (retain : Set C.Seam) (a : C.Total)
    (s : (C.closedSeams retain).Seam)
    (incident : (C.closedSeams retain).Incident a s) : C.SeamIncident retain a s.val := by
  obtain ⟨q, related, x, rfl⟩ := incident
  change Relation.EqvGen (C.closedSeams retain).relation a
    ⟨_, (C.closedSeams retain).toLeft s x⟩ at related
  rw [C.closedSeams_relation] at related
  exact ⟨x, related⟩

theorem incident_maps_compatible {small large : Set C.Seam} (a : C.Total)
    (kept : ∀ s ∈ large, C.SeamIncident large a s → s ∈ small) :
    ∀ s, (C.closedSeams large).Incident a s → ∀ x,
      MetricGluing.of C.Cell (C.glue small) ((C.closedSeams large).left s)
        ((C.closedSeams large).toLeft s x) =
      MetricGluing.of C.Cell (C.glue small) ((C.closedSeams large).right s)
        ((C.closedSeams large).toRight s x) := by
  intro s incident x
  exact C.seam_identified small s.val
    (kept s.val s.property (C.seamIncident_of_closedSeams_incident large a s incident)) x

/-- Keeping all incident seams preserves the point's entire declared equivalence class. -/
theorem eqvGen_iff_of_kept_incident {small large : Set C.Seam} (inclusion : small ⊆ large)
    (a : C.Total) (kept : ∀ s ∈ large, C.SeamIncident large a s → s ∈ small) (b : C.Total) :
    Relation.EqvGen (C.glue small) a b ↔ Relation.EqvGen (C.glue large) a b := by
  constructor
  · intro related
    exact related.mono (C.glue_mono inclusion)
  · intro related
    apply (C.point_eq_iff small a b).mp
    have related' : Relation.EqvGen (C.closedSeams large).relation a b := by
      rw [C.closedSeams_relation]
      exact related
    exact (C.closedSeams large).class_eq_of_incident_compatible a
      (MetricGluing.of C.Cell (C.glue small)) (C.incident_maps_compatible a kept) related'

/-- The canonical cut-restoration map is an isometry on a whole sufficiently small ball. -/
theorem exists_localForgetChart {small large : Set C.Seam} (inclusion : small ⊆ large)
    (a : C.Total) (kept : ∀ s ∈ large, C.SeamIncident large a s → s ∈ small) :
    Nonempty (MetricGluing.ForgetChart C.Cell (C.glue_mono inclusion) a) := by
  have finite : ∀ i, (MetricGluing.classIn C.Cell (C.closedSeams large).relation a i).Finite := by
    simpa only [C.closedSeams_relation] using C.finite_classIn large a
  have result := (C.closedSeams large).exists_radius_map_edist_le a finite
    (MetricGluing.of C.Cell (C.glue small)) (MetricGluing.of_lipschitz C.Cell (C.glue small))
    (C.incident_maps_compatible a kept)
  rw [C.closedSeams_relation] at result
  obtain ⟨r, positive, lower⟩ := result
  exact ⟨⟨r, positive,
    MetricGluing.forgetBallIsometry C.Cell (C.glue_mono inclusion) a
      (ENNReal.ofReal_pos.mpr positive) lower, fun _ => rfl⟩⟩

end Unfoldings.TriangleComplex
