module

public import Unfoldings.Metric.ClosedSeams
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Exact quotient topology for finite closed-seam gluings without bounded or complete cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I : Type*} [Finite I] {E : I → Type*} [∀ i, MetricSpace (E i)]
  (S : ClosedSeams E) (finite : ∀ a i, (classIn E S.relation a i).Finite)

include finite

/-- Finitely many cells and finite seam classes make the original cell projection closed.
Cells and seam domains may be unbounded and need not be complete. -/
theorem isClosedMap_point : IsClosedMap (point E S.relation) := by
  intro t closed_t
  rw [← isOpen_compl_iff]
  apply EMetric.isOpen_iff.mpr
  intro x outside
  obtain ⟨a, rfl⟩ := point_surjective E S.relation x
  let pieces (i : I) : Set (E i) := (@Sigma.mk I E i) ⁻¹' t
  have closed (i : I) : IsClosed (pieces i) := closed_t.preimage continuous_sigmaMk
  have radii (i : I) := MetricBarrier.exists_radius_near_closed (finite a i) (closed i)
  choose δ δpos δbound using radii
  obtain ⟨η, ηpos, common⟩ := MetricBarrier.exists_pos_le_of_finite δ δpos
  obtain ⟨ε, εpos, transport⟩ := S.class_transport a (finite a)
  let r := min ε η
  have positive : 0 < r := lt_min εpos ηpos
  refine ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.mpr positive, ?_⟩
  intro y near member
  obtain ⟨b, in_t, equal⟩ := member
  have close : edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r := by
    rw [equal, edist_comm]
    exact near
  obtain ⟨q, related, distance⟩ := exists_classPoint_of_edist_lt E S.relation a εpos
    (min_le_left ε η) (finite a) transport b close
  have in_piece : q ∈ pieces b.1 := δbound b.1 b.2 in_t q related
    (distance.trans_le ((min_le_right ε η).trans (common b.1)))
  apply outside
  exact ⟨⟨b.1, q⟩, in_piece, (point_eq_of_eqvGen E related).symm⟩

/-- The actual metric topology is the quotient of the original cells. -/
theorem isQuotientMap_point : Topology.IsQuotientMap (point E S.relation) :=
  (S.isClosedMap_point finite).isQuotientMap (continuous_point E S.relation)
    (point_surjective E S.relation)

theorem isClosedMap_toMetric : IsClosedMap (toMetric E S.relation) := by
  intro t closed_t
  have equality : point E S.relation '' (seamPoint E S.relation ⁻¹' t) =
      toMetric E S.relation '' t := by
    ext x
    constructor
    · rintro ⟨p, hp, equal⟩
      exact ⟨seamPoint E S.relation p, hp, equal⟩
    · rintro ⟨q, hq, equal⟩
      obtain ⟨p, rfl⟩ := Quot.exists_rep q
      exact ⟨p, hq, equal⟩
  rw [← equality]
  exact S.isClosedMap_point finite _ (closed_t.preimage continuous_quot_mk)

/-- Actual seam topology equals actual metric topology for finite closed-seam systems,
including unbounded graft cells. Finite seam classes are proved separately. -/
def seamHomeomorph : SeamQuotient E S.relation ≃ₜ Realization E S.relation :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (toMetric E S.relation)
      ⟨(exact_iff_toMetric_injective E S.relation).mp (S.exact_of_finite_classes finite),
        toMetric_surjective E S.relation⟩)
    (continuous_toMetric E S.relation) (S.isClosedMap_toMetric finite)

@[simp] theorem seamHomeomorph_seamPoint (a : Total E) :
    S.seamHomeomorph finite (seamPoint E S.relation a) = point E S.relation a := rfl

end Unfoldings.MetricGluing.ClosedSeams
