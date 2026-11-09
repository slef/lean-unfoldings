module

public import Unfoldings.Path.Chart

/-! Agreement at one positive chart time determines the whole initial interval. -/

@[expose] public section

namespace Path

variable {X : Type*} [PseudoEMetricSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  {a b c d : X} {p : Path a b} {q : Path c d} {s : Set X} {u : Set E}

theorem IsGeodesic.eq_initial_of_chart_sample (geodesic : p.IsGeodesic)
    (other : q.IsGeodesic) (chart : s ≃ᵢ u) {ε : unitInterval} (positive : 0 < ε)
    (inside : ∀ t ≤ ε, p t ∈ s) (other_inside : ∀ t ≤ ε, q t ∈ s)
    (start : a = c) (sample : p ε = q ε) : ∀ t ≤ ε, p t = q t := by
  have coordinates {x y : X} (hx : x ∈ s) (hy : y ∈ s) (equal : x = y) :
      (chart ⟨x, hx⟩).val = (chart ⟨y, hy⟩).val :=
    congrArg (fun z : s => (chart z).val) (Subtype.ext equal)
  have first := coordinates (inside 0 positive.le) (other_inside 0 positive.le)
    (p.source.trans (start.trans q.source.symm))
  have last := coordinates (inside ε le_rfl) (other_inside ε le_rfl) sample
  intro t ht
  let v := intervalFraction 0 ε t positive ⟨t.property.1, ht⟩
  have point : intervalParam 0 ε v = t :=
    intervalParam_fraction 0 ε t positive ⟨t.property.1, ht⟩
  have left := geodesic.chart_subpath_eq_lineMap chart positive.le (fun _ h => inside _ h.2) v
  have right := other.chart_subpath_eq_lineMap chart positive.le
    (fun _ h => other_inside _ h.2) v
  simp only [point] at left right
  have equal := left.trans ((congrArg₂ (fun x y => AffineMap.lineMap x y (v : ℝ))
    first last).trans right.symm)
  exact congrArg Subtype.val (chart.injective (Subtype.ext equal))

end Path
