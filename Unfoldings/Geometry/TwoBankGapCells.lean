module

public import Unfoldings.Geometry.TwoBankGap
public import Unfoldings.Geometry.PolygonalRayEquations
public import Unfoldings.Geometry.UnboundedArrangement

/-! Construct a finite closed convex decomposition of an actual two-bank Jordan gap. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

private theorem rightSector_interior_nonempty :
    (interior (planarSector (Real.pi / 2))).Nonempty := by
  rw [interior_planarSector (Real.pi / 2) (by simp)]
  exact ⟨(1 : ℂ) + polarRay (Real.pi / 2), 1, zero_lt_one, 1, zero_lt_one, by simp⟩

theorem twoBankGap_interior_nonempty :
    (interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)).Nonempty := by
  rw [twoBankGap, ← (R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
    positive_phase).image_interior]
  exact rightSector_interior_nonempty.image _

theorem twoBankGap_regular_closed :
    closure (interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase)) =
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase := by
  rw [twoBankGap, ← (R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero
    positive_phase).image_interior, ← (R.twoBankFrame Q first_outward first_nonzero last_outward
      last_nonzero positive_phase).image_closure,
    (convex_planarSector (Real.pi / 2)).closure_interior_eq_closure_of_nonempty_interior
      rightSector_interior_nonempty, (isClosed_planarSector (Real.pi / 2) (by simp)).closure_eq]

/-- Actual original and final bank supporting lines construct the unbounded gap cells. -/
theorem exists_twoBankGap_cell_cover (common : Q.start = R.start) :
    ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
      (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
        ⋃ i, cells i := by
  let lines := R.equations ∪ Q.equations
  have finite : lines.Finite := R.finite_equations.union Q.finite_equations
  let : Fintype lines := finite.fintype
  let f (i : lines) := i.val
  have nonzero (i : lines) : f i ≠ 0 := by
    rcases i.property with member | member
    · exact R.equations_ne_zero i.val member
    · exact Q.equations_ne_zero i.val member
  have support : ∀ z ∈ frontier
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase),
      ∃ i : lines, f i z = 0 := by
    intro z boundary
    rw [R.frontier_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common] at boundary
    rcases boundary with member | member
    · obtain ⟨l, line, zero⟩ := R.equations_cover z member
      exact ⟨⟨l, Or.inl line⟩, zero⟩
    · obtain ⟨l, line, zero⟩ := Q.equations_cover z member
      exact ⟨⟨l, Or.inr line⟩, zero⟩
  obtain ⟨S, finite_S, nonempty, cover⟩ :=
    AffineArrangement.exists_finite_unbounded_chamber_cover f nonzero
      (R.isClosed_twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)
      (R.twoBankGap_regular_closed Q first_outward first_nonzero last_outward last_nonzero
        positive_phase) support
  let : Fintype S := finite_S.fintype
  refine ⟨S, inferInstance, (fun i => AffineArrangement.closedChamber f i.val), ?_, ?_, ?_⟩
  · intro i
    refine ⟨AffineArrangement.isClosed_closedChamber f i.val,
      AffineArrangement.convex_closedChamber f i.val, ?_⟩
    rw [AffineArrangement.interior_closedChamber f i.val (nonempty i.val i.property).1]
    exact (nonempty i.val i.property).1
  · intro i j different
    exact AffineArrangement.disjoint_chamber_interiors f
      (nonempty i.val i.property).1 (nonempty j.val j.property).1
      (fun same => different (Subtype.ext same))
  · rw [cover]
    ext z
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]

end Unfoldings.PolygonalRay
