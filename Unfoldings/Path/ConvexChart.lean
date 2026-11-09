module

public import Unfoldings.Path.Chart
public import Unfoldings.Path.Segment

/-!
# Convex metric charts

Convex coordinate domains supply actual geodesics in the original metric.
An endpoint-distance bound confines every competing geodesic to an open ball,
so Euclidean ball charts also give uniqueness among all geodesics.
-/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.edist_source_le (geodesic : p.IsGeodesic) (t : unitInterval) :
    edist a (p t) ≤ edist a b := by
  have interval : edist (0 : unitInterval) t ≤ 1 := by
    rw [edist_dist, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_zero,
      zero_sub, abs_neg, abs_of_nonneg t.property.1]
    exact (ENNReal.ofReal_le_ofReal t.property.2).trans_eq (by simp)
  simpa only [Path.source, mul_one] using
    (geodesic 0 t).trans_le (by simpa using mul_le_mul_right interval (edist a b))

/-- This bound confines every geodesic with the given endpoints, even when
the ambient metric has other routes outside the ball. -/
theorem IsGeodesic.mem_eball (geodesic : p.IsGeodesic) (c : X) (r : ℝ≥0∞)
    (margin : edist a c + edist a b < r) (t : unitInterval) :
    p t ∈ Metric.eball c r := by
  change edist (p t) c < r
  exact (edist_triangle (p t) a c).trans_lt
    ((add_le_add (by simpa only [edist_comm] using geodesic.edist_source_le t) le_rfl).trans_lt
      (by simpa only [add_comm] using margin))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set X} {u : Set E}

/-- A convex isometric chart constructs a shortest path in the original space. -/
theorem exists_geodesic_in_chart (chart : s ≃ᵢ u) (convex : Convex ℝ u)
    (ha : a ∈ s) (hb : b ∈ s) :
    ∃ p : Path a b, p.IsGeodesic ∧ ∀ t, p t ∈ s := by
  let x := chart ⟨a, ha⟩
  let y := chart ⟨b, hb⟩
  let q := (Path.segment x.val y.val).codRestrict u x.property y.property
    (fun t => convex.lineMap_mem x.property y.property t.property)
  let f : u → X := Subtype.val ∘ chart.symm
  have isometry : Isometry f := (isometry_subtype_coe (s := s)).comp chart.symm.isometry
  have first : f x = a := congrArg Subtype.val (chart.symm_apply_apply ⟨a, ha⟩)
  have last : f y = b := congrArg Subtype.val (chart.symm_apply_apply ⟨b, hb⟩)
  let p : Path a b :=
    { toFun t := f (q t)
      continuous_toFun := isometry.continuous.comp q.continuous
      source' := (congrArg f q.source).trans first
      target' := (congrArg f q.target).trans last }
  refine ⟨p, ?_, fun t => (chart.symm (q t)).property⟩
  have geodesic : (Path.segment x.val y.val).IsGeodesic :=
    (Path.segment x.val y.val).isGeodesic_of_lipschitz (segment_lipschitz _ _)
  have restricted := geodesic.codRestrict u x.property y.property
    (fun t => convex.lineMap_mem x.property y.property t.property)
  intro v w
  change edist (f (q v)) (f (q w)) = edist a b * edist v w
  rw [isometry.edist_eq, ← first, ← last, isometry.edist_eq]
  exact restricted v w

variable [StrictConvexSpace ℝ E]

/-- In a Euclidean ball chart the endpoint margin ensures global geodesic
uniqueness: both paths are automatically contained in the chart. -/
theorem IsGeodesic.eq_of_eball_chart (geodesic : p.IsGeodesic) {q : Path a b}
    (other : q.IsGeodesic) (c : X) (r : ℝ≥0∞)
    (chart : Metric.eball c r ≃ᵢ u)
    (margin : edist a c + edist a b < r) : p = q := by
  have inside := geodesic.mem_eball c r margin
  have other_inside := other.mem_eball c r margin
  apply geodesic.eq_of_chart other chart
    (by simpa only [Path.source] using inside 0)
    (by simpa only [Path.target] using inside 1) inside other_inside

end Path
