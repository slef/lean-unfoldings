module

public import Unfoldings.Path.Restriction
public import Unfoldings.Path.Subpath
public import Unfoldings.Path.Straight

/-!
# Geodesics in isometric charts

The hypotheses refer to the actual metric restricted to the chart domain.
A geodesic contained in that domain becomes an affinely parameterized segment
in Euclidean coordinates. Two such geodesics with the same endpoints coincide.
The subpath version applies when only one parameter interval lies in the chart.
-/

@[expose] public section

namespace Path

variable {X : Type*} [PseudoEMetricSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  {a b : X} {p q : Path a b} {s : Set X} {u : Set E}

/-- Chart coordinates of a contained geodesic are the endpoint chord with its
original constant-speed parameter. -/
theorem IsGeodesic.chart_eq_lineMap (geodesic : p.IsGeodesic) (chart : s ≃ᵢ u)
    (ha : a ∈ s) (hb : b ∈ s) (inside : ∀ t, p t ∈ s) (t : unitInterval) :
    (chart ⟨p t, inside t⟩).val =
      AffineMap.lineMap (chart ⟨a, ha⟩).val (chart ⟨b, hb⟩).val (t : ℝ) := by
  let f : s → E := Subtype.val ∘ chart
  have isometry : Isometry f := (isometry_subtype_coe (s := u)).comp chart.isometry
  exact (geodesic.codRestrict s ha hb inside).map_eq_lineMap f isometry.lipschitzWith
    (isometry.edist_eq _ _) t

/-- Straightness in a chart gives uniqueness without requiring that every
geodesic between the endpoints remain in the chart. -/
theorem IsGeodesic.eq_of_chart (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (chart : s ≃ᵢ u) (ha : a ∈ s) (hb : b ∈ s)
    (inside : ∀ t, p t ∈ s) (other_inside : ∀ t, q t ∈ s) : p = q := by
  ext t
  have coordinates := (geodesic.chart_eq_lineMap chart ha hb inside t).trans
    (other.chart_eq_lineMap chart ha hb other_inside t).symm
  exact congrArg Subtype.val (chart.injective (Subtype.ext coordinates))

/-- Local straightness for any ordered parameter interval lying in the domain. -/
theorem IsGeodesic.chart_subpath_eq_lineMap (geodesic : p.IsGeodesic)
    (chart : s ≃ᵢ u) {r t : unitInterval} (ordered : r ≤ t)
    (inside : ∀ v ∈ Set.Icc r t, p v ∈ s) (v : unitInterval) :
    (chart ⟨p (intervalParam r t v),
      inside _ (intervalParam_mem_Icc ordered v)⟩).val =
      AffineMap.lineMap (chart ⟨p r, inside r ⟨le_rfl, ordered⟩⟩).val
        (chart ⟨p t, inside t ⟨ordered, le_rfl⟩⟩).val (v : ℝ) :=
  (geodesic.subpath r t).chart_eq_lineMap chart
    (inside r ⟨le_rfl, ordered⟩) (inside t ⟨ordered, le_rfl⟩)
    (fun v => inside _ (intervalParam_mem_Icc ordered v)) v

end Path
