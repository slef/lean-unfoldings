module

public import Unfoldings.Path.Geodesic
public import Mathlib.Analysis.Convex.StrictConvexBetween

/-! Saturated nonexpanding images of metric geodesics are straight. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.edist_add_edist_eq (geodesic : p.IsGeodesic)
    {s u t : unitInterval} (first : s ≤ u) (last : u ≤ t) :
    edist (p s) (p u) + edist (p u) (p t) = edist (p s) (p t) := by
  have first' : (s : ℝ) ≤ (u : ℝ) := first
  have last' : (u : ℝ) ≤ (t : ℝ) := last
  have interval : dist s u + dist u t = dist s t := by
    change |(s : ℝ) - (u : ℝ)| + |(u : ℝ) - (t : ℝ)| = |(s : ℝ) - (t : ℝ)|
    rw [abs_of_nonpos (sub_nonpos.mpr first'), abs_of_nonpos (sub_nonpos.mpr last'),
      abs_of_nonpos (sub_nonpos.mpr (first'.trans last'))]
    ring
  rw [geodesic s u, geodesic u t, geodesic s t, ← mul_add]
  congr 1
  rw [edist_dist, edist_dist, edist_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg, interval]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- If the endpoint chord saturates a nonexpanding map, the geodesic maps into that segment. -/
theorem IsGeodesic.map_mem_segment (geodesic : p.IsGeodesic) (f : X → E)
    (nonexpanding : LipschitzWith 1 f) {s u t : unitInterval} (first : s ≤ u) (last : u ≤ t)
    (saturated : edist (f (p s)) (f (p t)) = edist (p s) (p t)) :
    f (p u) ∈ segment ℝ (f (p s)) (f (p t)) := by
  have left := nonexpanding.edist_le_mul (p s) (p u)
  have right := nonexpanding.edist_le_mul (p u) (p t)
  simp only [ENNReal.coe_one, one_mul] at left right
  have equal : edist (f (p s)) (f (p u)) + edist (f (p u)) (f (p t)) =
      edist (f (p s)) (f (p t)) := by
    apply le_antisymm
    · exact (add_le_add left right).trans_eq
        ((geodesic.edist_add_edist_eq first last).trans saturated.symm)
    · exact edist_triangle _ _ _
  have distance : dist (f (p s)) (f (p u)) + dist (f (p u)) (f (p t)) =
      dist (f (p s)) (f (p t)) := by
    rw [edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at equal
    have real_equal := congrArg ENNReal.toReal equal
    simpa only [ENNReal.toReal_ofReal (add_nonneg dist_nonneg dist_nonneg),
      ENNReal.toReal_ofReal dist_nonneg] using real_equal
  exact mem_segment_iff_wbtw.mpr (dist_add_dist_eq_iff.mp distance)

/-- A constant-speed Euclidean geodesic has exactly the usual affine parameterization. -/
theorem IsGeodesic.eq_lineMap {a b : E} {p : Path a b} (geodesic : p.IsGeodesic)
    (t : unitInterval) : p t = AffineMap.lineMap a b (t : ℝ) := by
  have distances (s t : unitInterval) : dist (p s) (p t) = dist a b * dist s t := by
    have equal := congrArg ENNReal.toReal (geodesic s t)
    simpa only [edist_dist, ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg] using equal
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · have first := distances 0 t
    simpa only [Path.source, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_zero, zero_sub,
      abs_neg, abs_of_nonneg t.property.1, mul_comm] using first
  · have last := distances t 1
    simpa only [Path.target, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_one,
      abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub, mul_comm] using last

/-- Saturation at the endpoints makes the entire nonexpanding image a straight radial path. -/
theorem IsGeodesic.map_eq_lineMap (geodesic : p.IsGeodesic) (f : X → E)
    (nonexpanding : LipschitzWith 1 f) (saturated : edist (f a) (f b) = edist a b)
    (t : unitInterval) : f (p t) = AffineMap.lineMap (f a) (f b) (t : ℝ) := by
  let q := p.map nonexpanding.continuous
  have speed : LipschitzWith (nndist (f a) (f b)) q := by
    intro s t
    have bound := nonexpanding.edist_le_mul (p s) (p t)
    simp only [ENNReal.coe_one, one_mul] at bound
    change edist (f (p s)) (f (p t)) ≤ _
    rw [← edist_nndist, saturated]
    exact bound.trans_eq (geodesic s t)
  exact (q.isGeodesic_of_lipschitz speed).eq_lineMap t

end Path
