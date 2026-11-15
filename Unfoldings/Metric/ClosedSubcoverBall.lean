module

public import Unfoldings.Metric.ClosedSeams
public import Unfoldings.Metric.BallChartTransport

/-! An isometric subcover containing every incident cell contains a whole small intrinsic ball. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I : Type*} {E : I → Type*} [∀ i, MetricSpace (E i)]
  (S : ClosedSeams E) {X : Type*} [EMetricSpace X]

/-- Closed seam transport derives whole-ball coverage from actual incident cells.
No whole-ball surjectivity or manifold certificate is supplied. -/
theorem exists_isometric_subcover_ball (a : Total E)
    (finite : ∀ i, (classIn E S.relation a i).Finite)
    (f : X → Realization E S.relation) (isometric : Isometry f) (source : X)
    (center : f source = point E S.relation a)
    (covered : ∀ i, (classIn E S.relation a i).Nonempty → ∀ x : E i,
      ∃ z : X, f z = of E S.relation i x) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (point E S.relation a) (ENNReal.ofReal r),
        ∀ z, (B z).val = f z.val := by
  obtain ⟨r, positive, transport⟩ := S.class_transport a finite
  let map : Metric.eball source (ENNReal.ofReal r) →
      Metric.eball (point E S.relation a) (ENNReal.ofReal r) := fun z =>
    ⟨f z.val, by
      change edist (f z.val) (point E S.relation a) < ENNReal.ofReal r
      rw [← center, isometric.edist_eq]
      exact z.property⟩
  have isometric_map : Isometry map := fun x y => isometric x.val y.val
  have surjective : Function.Surjective map := by
    intro y
    obtain ⟨b, represents⟩ := point_surjective E S.relation y.val
    have near : edist (point E S.relation a) (point E S.relation b) < ENNReal.ofReal r := by
      rw [represents, edist_comm]
      exact y.property
    obtain ⟨q, related, _close⟩ := exists_classPoint_of_edist_lt E S.relation a positive
      le_rfl finite transport b near
    obtain ⟨z, hz⟩ := covered b.1 ⟨q, related⟩ b.2
    have source_near : edist z source < ENNReal.ofReal r := by
      rw [← isometric.edist_eq, hz, center]
      change edist (point E S.relation b) (point E S.relation a) < ENNReal.ofReal r
      rw [represents]
      exact y.property
    refine ⟨⟨z, source_near⟩, ?_⟩
    apply Subtype.ext
    exact hz.trans represents
  exact ⟨r, positive, ⟨Equiv.ofBijective map ⟨isometric_map.injective, surjective⟩, isometric_map⟩,
    fun _ => rfl⟩

end Unfoldings.MetricGluing.ClosedSeams
