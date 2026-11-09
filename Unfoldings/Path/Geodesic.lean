module

public import Unfoldings.Path.Length

/-! Metric geodesics as distance-preserving constant-speed paths. -/

@[expose] public section

open scoped ENNReal NNReal

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X}

/-- A path realizes metric distance at constant speed on every subinterval. -/
def IsGeodesic (p : Path a b) : Prop :=
  ∀ s t : unitInterval, edist (p s) (p t) = edist a b * edist s t

theorem IsGeodesic.eLength_eq_edist {p : Path a b} (geodesic : p.IsGeodesic) :
    p.eLength = edist a b := by
  by_cases finite : edist a b = ⊤
  · rw [finite]
    exact top_unique (finite ▸ p.edist_le_eLength)
  · have speed : LipschitzWith (edist a b).toNNReal p := by
      intro s t
      rw [geodesic s t, ENNReal.coe_toNNReal finite]
    exact le_antisymm ((p.eLength_le_of_lipschitz speed).trans_eq (ENNReal.coe_toNNReal finite))
      p.edist_le_eLength

theorem IsGeodesic.isLengthMinimizing {p : Path a b} (geodesic : p.IsGeodesic) :
    p.IsLengthMinimizing := by
  intro q
  rw [geodesic.eLength_eq_edist]
  exact q.edist_le_eLength

end Path

namespace Path

variable {X : Type*} [MetricSpace X] {a b : X}

/-- A speed bound by endpoint distance forces distance realization on every subinterval. -/
theorem isGeodesic_of_lipschitz (p : Path a b) (speed : LipschitzWith (nndist a b) p) :
    p.IsGeodesic := by
  have along (s t : unitInterval) : dist (p s) (p t) = dist a b * dist s t := by
    wlog ordered : s ≤ t generalizing s t
    · simpa only [dist_comm] using this t s (le_of_not_ge ordered)
    have ordered' : (s : ℝ) ≤ (t : ℝ) := ordered
    have first : dist a (p s) ≤ dist a b * (s : ℝ) := by
      have bound := speed.dist_le_mul (0 : unitInterval) s
      change dist (p 0) (p s) ≤ dist a b * |0 - (s : ℝ)| at bound
      simpa only [Path.source, zero_sub, abs_neg, abs_of_nonneg s.property.1] using bound
    have last : dist (p t) b ≤ dist a b * (1 - (t : ℝ)) := by
      have bound := speed.dist_le_mul t (1 : unitInterval)
      change dist (p t) (p 1) ≤ dist a b * |(t : ℝ) - 1| at bound
      simpa only [Path.target, abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] using bound
    have middle : dist (p s) (p t) ≤ dist a b * ((t : ℝ) - (s : ℝ)) := by
      simpa only [coe_nndist, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr ordered'), neg_sub] using speed.dist_le_mul s t
    have triangle₁ := dist_triangle a (p s) b
    have triangle₂ := dist_triangle (p s) (p t) b
    have interval : dist s t = (t : ℝ) - (s : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ordered'), neg_sub]
    rw [interval]
    nlinarith
  intro s t
  rw [edist_dist, along, ENNReal.ofReal_mul dist_nonneg, ← edist_dist, ← edist_dist]

theorem isGeodesic_of_eLength_eq_of_lipschitz (p : Path a b) (equal : p.eLength = edist a b)
    (speed : LipschitzWith p.eLength.toNNReal p) : p.IsGeodesic := by
  apply p.isGeodesic_of_lipschitz
  simpa only [equal, edist_nndist, ENNReal.toNNReal_coe] using speed

end Path
