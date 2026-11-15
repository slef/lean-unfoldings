module

public import Unfoldings.Geometry.TwoBankGapCells
public import Unfoldings.Geometry.FiniteRegionGermMetric

/-! Intrinsic active-cone models at all actual Jordan-gap corners, including reentrant banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.AffineArrangement

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite I] [Finite J]
  (f : J → I → E →ᵃ[ℝ] ℝ) (signs : J → I → Bool)

/-- The cone chart applies to the actual named region, retaining its physical coordinates. -/
theorem exists_regionGerm_ball_isometry_of_cover {s : Set E}
    (cover : s = ⋃ j, closedChamber (f j) (signs j)) (x : PolygonalPoint s) :
    ∃ r : ℝ, 0 < r ∧ ∃ a : PolygonalPoint (translatedRegionGerm f signs x.val),
      a.val = x.val ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
        Metric.eball a (ENNReal.ofReal r), ∀ z, (A z).val.val = z.val.val := by
  subst s
  exact exists_regionGerm_ball_isometry f signs x

end Unfoldings.AffineArrangement

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)

/-- The actual supporting lines of both polygonal banks, including their infinite tails. -/
def bankEquation (i : ↥(R.equations ∪ Q.equations)) : ℂ →ᵃ[ℝ] ℝ := i.val

variable (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- Keep the original bank equations and selected chamber signs in the gap decomposition. -/
theorem exists_twoBankGap_chamber_cover (common : Q.start = R.start) :
    ∃ S : Set (↥(R.equations ∪ Q.equations) → Bool), S.Finite ∧
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
        ⋃ σ ∈ S, AffineArrangement.closedChamber (R.bankEquation Q) σ := by
  let lines := R.equations ∪ Q.equations
  let : Fintype lines := (R.finite_equations.union Q.finite_equations).fintype
  have nonzero (i : lines) : R.bankEquation Q i ≠ 0 := by
    rcases i.property with member | member
    · exact R.equations_ne_zero i.val member
    · exact Q.equations_ne_zero i.val member
  have support : ∀ z ∈ frontier
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase),
      ∃ i : lines, R.bankEquation Q i z = 0 := by
    intro z boundary
    rw [R.frontier_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common] at boundary
    rcases boundary with member | member
    · obtain ⟨l, line, zero⟩ := R.equations_cover z member
      exact ⟨⟨l, Or.inl line⟩, zero⟩
    · obtain ⟨l, line, zero⟩ := Q.equations_cover z member
      exact ⟨⟨l, Or.inr line⟩, zero⟩
  obtain ⟨S, finite, _, cover⟩ :=
    AffineArrangement.exists_finite_unbounded_chamber_cover (R.bankEquation Q) nonzero
      (R.isClosed_twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)
      (R.twoBankGap_regular_closed Q first_outward first_nonzero last_outward last_nonzero
        positive_phase) support
  exact ⟨S, finite, cover⟩

/-- Every point of the actual gap has a whole intrinsic ball isometric to its constructed
active cone union. This includes all bank vertices and does not assume a corner-angle model. -/
theorem exists_twoBankGap_corner_cone_isometries (common : Q.start = R.start) :
    ∃ S : Set (↥(R.equations ∪ Q.equations) → Bool), S.Finite ∧
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
        ⋃ σ ∈ S, AffineArrangement.closedChamber (R.bankEquation Q) σ ∧
      ∀ x : PolygonalPoint
        (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase),
      ∃ r : ℝ, 0 < r ∧
      ∃ a : PolygonalPoint (AffineArrangement.translatedRegionGerm
        (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x.val),
        a.val = x.val ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball a (ENNReal.ofReal r), ∀ z, (A z).val.val = z.val.val := by
  obtain ⟨S, finite, cover⟩ := R.exists_twoBankGap_chamber_cover Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common
  let : Fintype ↥(R.equations ∪ Q.equations) :=
    (R.finite_equations.union Q.finite_equations).fintype
  let : Fintype S := finite.fintype
  refine ⟨S, finite, cover, ?_⟩
  intro x
  apply AffineArrangement.exists_regionGerm_ball_isometry_of_cover
    (fun _ : S => R.bankEquation Q) (fun σ => σ.val) _ x
  rw [cover]
  ext z
  simp only [Set.mem_iUnion, Subtype.exists, exists_prop]

end Unfoldings.PolygonalRay
