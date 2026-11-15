module

public import Unfoldings.Geometry.TwoBankGapMetric
public import Unfoldings.Metric.PolygonalBoundaryCover

/-! Exact boundary-only finite planar-cell gluing models of the actual Jordan gaps. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- Construct actual finite complete planar cells, exact physical identifications and
boundary-only seam support. The realized metric and topology are those of the actual gap. -/
theorem exists_twoBankGap_boundary_gluing (common : Q.start = R.start) :
    ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
      (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
      (∀ i x, x ∈ MetricGluing.seamSupport (fun j => cells j)
        (MetricGluing.distinctCoincident cells) i → x.val ∉ interior (cells i)) ∧
      ∃ A : MetricGluing.Realization (fun i => cells i) (MetricGluing.distinctCoincident cells) ≃ᵢ
        PolygonalPoint
          (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase),
        (∀ i x, (A (MetricGluing.of (fun j => cells j)
          (MetricGluing.distinctCoincident cells) i x)).val = x.val) ∧
        CompleteSpace (MetricGluing.Realization (fun i => cells i)
          (MetricGluing.distinctCoincident cells)) ∧
        ContractibleSpace (MetricGluing.Realization (fun i => cells i)
          (MetricGluing.distinctCoincident cells)) := by
  obtain ⟨I, inst, cells, properties, disjoint, cover⟩ :=
    R.exists_twoBankGap_cell_cover Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common
  let : Fintype I := inst
  let A := MetricGluing.boundaryCoverIsometryEquiv cells (fun i => (properties i).1)
    (fun i => (properties i).2.1) cover
  refine ⟨I, inst, cells, properties, disjoint, ?_, A, ?_, ?_, ?_⟩
  · exact MetricGluing.distinctCoincident_seamSupport_boundary_of_convex cells
      (fun i => (properties i).1) (fun i => (properties i).2.1)
      (fun i => (properties i).2.2) disjoint
  · intro i x
    rfl
  · let : CompleteSpace (PolygonalPoint
        (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :=
      R.twoBankGap_complete Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common
    exact A.completeSpace
  · let : ContractibleSpace (PolygonalPoint
        (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :=
      R.twoBankGap_contractible Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common
    exact A.toHomeomorph.contractibleSpace

end Unfoldings.PolygonalRay
