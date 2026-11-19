module

public import Unfoldings.Cone.SectorPairBall
public import Mathlib.Topology.UnitInterval

/-! Attach two actual sector charts with closed edge parameters on each common ray. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.MetricGluing.SectorPairChart

variable {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {glue : Total X → Total X → Prop} {a : Bool → Total X}
  {θ : ℝ} {pos : 0 < θ} {small : θ < 2 * Real.pi} {R : ℝ}
  (A : SectorPairChart X a pos small R) {length : ℝ}

local notation "origin" => complementarySectorOrigin pos small
local notation "ρ" => ENNReal.ofReal R

/-- The two common geometric rays, in roof coordinates. -/
def bankRay (θ : ℝ) (side : Bool) (s : ℝ) : ℂ :=
  if side then (s : ℂ) * polarRay θ else (s : ℂ)

variable (mark : ∀ b : Bool, Bool → unitInterval → X (a b).1)

local notation "markAt[" b "," side "," t "]" => (Sigma.mk (Sigma.fst (a b)) (mark b side t))

/-- Exact closed-interval arclengths give every common point of the two local charts
a genuine originally glued pair of marks. -/
theorem shared_of_bankRays_lengths (len : Bool → ℝ) (length_bound : ∀ side, R ≤ len side)
    (distance : ∀ (b side : Bool) (t : unitInterval),
      edist (mark b side t) (a b).2 = ENNReal.ofReal (t.val * len side))
    (coordinates : ∀ (b side : Bool) (t : unitInterval) (near : edist (mark b side t) (a b).2 < ρ),
      (A.chart b ⟨mark b side t, near⟩).val.val = bankRay θ side (t.val * len side))
    (joined : ∀ (side : Bool) (t : unitInterval),
      point X glue markAt[false,side,t] = point X glue markAt[true,side,t]) :
    ∀ (b c : Bool) (x : Metric.eball (origin b) ρ) (y : Metric.eball (origin c) ρ),
      x.val.val = y.val.val →
        point X glue (A.inverseTag b x) = point X glue (A.inverseTag c y) := by
  have length_positive (side : Bool) : 0 < len side := A.positive.trans_le (length_bound side)
  have realize_ray (side : Bool) (s : ℝ≥0) (bound : (s : ℝ) < R)
      (x : Metric.eball (origin false) ρ) (y : Metric.eball (origin true) ρ)
      (hx : x.val.val = bankRay θ side s) (hy : y.val.val = bankRay θ side s) :
      point X glue (A.inverseTag false x) = point X glue (A.inverseTag true y) := by
    let t : unitInterval := ⟨(s : ℝ) / len side, div_nonneg s.property (length_positive side).le,
      (div_le_one (length_positive side)).mpr (bound.le.trans (length_bound side))⟩
    have product : t.val * len side = (s : ℝ) := div_mul_cancel₀ _ (length_positive side).ne'
    have fit (b : Bool) : edist (mark b side t) (a b).2 < ρ :=
      (distance b side t).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg t.property.1 (length_positive side).le)).mpr
          (product.trans_lt bound))
    let u (b : Bool) : Metric.eball (a b).2 ρ := ⟨mark b side t, fit b⟩
    have at_ray (b : Bool) : (A.chart b (u b)).val.val = bankRay θ side s :=
      (coordinates b side t (fit b)).trans (congrArg (bankRay θ side) product)
    have ax : A.chart false (u false) = x :=
      Subtype.ext (PolygonalPoint.ext ((at_ray false).trans hx.symm))
    have ay : A.chart true (u true) = y :=
      Subtype.ext (PolygonalPoint.ext ((at_ray true).trans hy.symm))
    rw [inverseTag, (A.chart false).symm_apply_eq.mpr ax.symm,
      inverseTag, (A.chart true).symm_apply_eq.mpr ay.symm]
    exact joined side t
  have cross (x : Metric.eball (origin false) ρ) (y : Metric.eball (origin true) ρ)
      (equal : x.val.val = y.val.val) :
      point X glue (A.inverseTag false x) = point X glue (A.inverseTag true y) := by
    have both : x.val.val ∈ closedAngularSector θ ∩ complementarySector θ :=
      ⟨x.val.property, equal.symm ▸ y.val.property⟩
    rw [closedAngularSector_inter_complementary θ pos small] at both
    obtain ⟨side, s, eq⟩ : ∃ (side : Bool) (s : ℝ≥0), x.val.val = bankRay θ side s := by
      rcases both with ⟨s, same⟩ | ⟨s, same⟩
      · exact ⟨false, s, same.symm⟩
      · exact ⟨true, s, same.symm⟩
    have norm : ‖bankRay θ side s‖ = (s : ℝ) := by
      cases side <;> simp [bankRay, norm_polarRay]
    have bound := x.property
    change edist x.val (origin false) < _ at bound
    rw [edist_complementarySectorOrigin, eq, edist_dist, dist_zero_right, norm] at bound
    exact realize_ray side s ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.property).mp bound)
      x y eq (equal.symm.trans eq)
  intro b c x y equal
  cases b <;> cases c
  · obtain rfl : x = y := Subtype.ext (PolygonalPoint.ext equal)
    rfl
  · exact cross x y equal
  · exact (cross y x equal.symm).symm
  · obtain rfl : x = y := Subtype.ext (PolygonalPoint.ext equal)
    rfl

/-- Exact closed-interval arclengths give every common point of the two local charts
a genuine originally glued pair of marks. -/
theorem shared_of_bankRays (length_bound : R ≤ length)
    (distance : ∀ (b side : Bool) (t : unitInterval),
      edist (mark b side t) (a b).2 = ENNReal.ofReal (t.val * length))
    (coordinates : ∀ (b side : Bool) (t : unitInterval) (near : edist (mark b side t) (a b).2 < ρ),
      (A.chart b ⟨mark b side t, near⟩).val.val = bankRay θ side (t.val * length))
    (joined : ∀ (side : Bool) (t : unitInterval),
      point X glue markAt[false,side,t] = point X glue markAt[true,side,t]) :
    ∀ (b c : Bool) (x : Metric.eball (origin b) ρ) (y : Metric.eball (origin c) ρ),
      x.val.val = y.val.val →
        point X glue (A.inverseTag b x) = point X glue (A.inverseTag c y) :=
  A.shared_of_bankRays_lengths mark (fun _ => length) (fun _ => length_bound)
    distance coordinates joined

end Unfoldings.MetricGluing.SectorPairChart
