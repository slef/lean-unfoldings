module

public import Unfoldings.Metric.Route
public import Unfoldings.Metric.BallParametrization
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Constructed intrinsic polygonal metrics on Euclidean subsets

A step has Euclidean cost precisely when its whole closed segment stays in
the subset; other steps have infinite cost. Finite routes construct the
intrinsic extended metric. The separate point type keeps this metric distinct
from the ambient subspace metric. Ambient distance gives separation and a
nonexpanding projection. Convex patches and whole interior balls are genuinely
isometric, and a star center makes all distances finite.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure PolygonalPoint (s : Set E) where
  val : E
  property : val ∈ s

namespace PolygonalPoint

variable {s : Set E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[ext] theorem ext {x y : PolygonalPoint s} (equal : x.val = y.val) : x = y := by
  cases x
  cases y
  cases equal
  rfl

def stepCost (x y : PolygonalPoint s) : ℝ≥0∞ := by
  classical
  exact if segment ℝ x.val y.val ⊆ s then edist x.val y.val else ⊤

theorem stepCost_comm (x y : PolygonalPoint s) : stepCost x y = stepCost y x := by
  unfold stepCost
  conv_lhs => rw [segment_symm ℝ x.val y.val, edist_comm x.val y.val]

theorem ambient_edist_le_distance (x y : PolygonalPoint s) :
    edist x.val y.val ≤ Route.distance stepCost x y := by
  apply Route.le_distance stepCost (fun x y : PolygonalPoint s => edist x.val y.val)
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · simp only [stepCost, ite_eq_left inside, le_refl]
  · simp only [stepCost, ite_eq_right inside, le_top]

instance : EMetricSpace (PolygonalPoint s) :=
  { Route.pseudoEMetricSpace stepCost stepCost_comm with
    eq_of_edist_eq_zero := by
      intro x y zero
      apply PolygonalPoint.ext
      apply edist_eq_zero.mp
      change Route.distance stepCost x y = 0 at zero
      exact le_antisymm ((ambient_edist_le_distance x y).trans_eq zero) bot_le }

theorem ambient_lipschitz : LipschitzWith 1 (PolygonalPoint.val (s := s)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  exact ambient_edist_le_distance x y

theorem edist_eq_of_segment {x y : PolygonalPoint s}
    (inside : segment ℝ x.val y.val ⊆ s) : edist x y = edist x.val y.val := by
  apply le_antisymm
  · change Route.distance stepCost x y ≤ _
    exact (Route.distance_le_cost stepCost x y).trans_eq (by
      simp only [stepCost, ite_eq_left inside])
  · exact ambient_edist_le_distance x y

def includeConvex (u : Set E) (included : u ⊆ s) : u → PolygonalPoint s :=
  fun x => ⟨x.val, included x.property⟩

theorem includeConvex_isometry (u : Set E) (convex : Convex ℝ u) (included : u ⊆ s) :
    Isometry (includeConvex u included) := by
  intro x y
  exact edist_eq_of_segment ((convex.segment_subset x.property y.property).trans included)

theorem edist_ne_top_of_starConvex {center : E} (star : StarConvex ℝ center s)
    (inside : center ∈ s) (x y : PolygonalPoint s) : edist x y ≠ ⊤ := by
  let c : PolygonalPoint s := ⟨center, inside⟩
  have first : edist x c = edist x.val center := by
    rw [edist_comm x c]
    exact (edist_eq_of_segment (star.segment_subset x.property)).trans (edist_comm _ _)
  have last : edist c y = edist center y.val := edist_eq_of_segment (star.segment_subset y.property)
  apply ne_top_of_le_ne_top _ (edist_triangle x c y)
  rw [first, last]
  exact ENNReal.add_ne_top.mpr ⟨edist_ne_top _ _, edist_ne_top _ _⟩

theorem hasMetricBallChart_of_ball {x : PolygonalPoint s} {r : ℝ} (positive : 0 < r)
    (included : Metric.ball x.val r ⊆ s) : HasMetricBallChart E x := by
  let f := includeConvex (Metric.ball x.val r) included
  have isometry : Isometry f := includeConvex_isometry _ (convex_ball x.val r) included
  apply HasMetricBallChart.of_isometric_ball positive f isometry
    (PolygonalPoint.ext rfl)
  intro y near
  have center_eq : f ⟨x.val, Metric.mem_ball_self positive⟩ = x :=
    PolygonalPoint.ext rfl
  rw [center_eq] at near
  have ambient : edist y.val x.val < ENNReal.ofReal r :=
    (ambient_lipschitz.edist_le_mul y x).trans_lt (by
      simpa only [ENNReal.coe_one, one_mul] using near)
  have in_ball : y.val ∈ Metric.ball x.val r := by
    rw [Metric.mem_ball]
    rw [edist_dist] at ambient
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp ambient
  exact ⟨⟨y.val, in_ball⟩, PolygonalPoint.ext rfl⟩

/-- Enlarging a region can shorten its intrinsic distances. -/
def inclusion {t : Set E} (included : s ⊆ t) : PolygonalPoint s → PolygonalPoint t :=
  fun x => ⟨x.val, included x.property⟩

theorem inclusion_lipschitz {t : Set E} (included : s ⊆ t) :
    LipschitzWith 1 (inclusion included) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change edist (inclusion included x) (inclusion included y) ≤
    Route.distance (stepCost (s := s)) x y
  apply Route.le_distance (stepCost (s := s))
    (fun a b => edist (inclusion included a) (inclusion included b))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · rw [stepCost, ite_eq_left inside]
    exact (edist_eq_of_segment (x := inclusion included a) (y := inclusion included b)
      (inside.trans included)).le
  · simp only [stepCost, ite_eq_right inside, le_top]

def toSubtype (x : PolygonalPoint s) : s := ⟨x.val, x.property⟩

theorem continuous_toSubtype : Continuous (toSubtype (s := s)) :=
  ambient_lipschitz.continuous.subtype_mk _

def ofSubtype (x : s) : PolygonalPoint s := ⟨x.val, x.property⟩

theorem continuous_ofSubtype (is_open : IsOpen s) : Continuous (ofSubtype (s := s)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, positive, included⟩ := Metric.isOpen_iff.mp is_open x.val x.property
  apply EMetric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min (ENNReal.ofReal r) ε, lt_min (ENNReal.ofReal_pos.mpr positive) hε, ?_⟩
  intro y near
  have in_ball : y.val ∈ Metric.ball x.val r := by
    rw [Metric.mem_ball]
    have bound : edist y.val x.val < ENNReal.ofReal r := lt_of_lt_of_le near (min_le_left _ _)
    rw [edist_dist] at bound
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp bound
  have segment_inside :=
    ((convex_ball x.val r).segment_subset in_ball (Metric.mem_ball_self positive)).trans included
  exact (edist_eq_of_segment segment_inside).trans_lt (lt_of_lt_of_le near (min_le_right _ _))

/-- On open subsets the intrinsic metric has exactly the ambient topology. -/
def openHomeomorph (is_open : IsOpen s) : PolygonalPoint s ≃ₜ s where
  toFun := toSubtype
  invFun := ofSubtype
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toSubtype
  continuous_invFun := continuous_ofSubtype is_open

end PolygonalPoint
end Unfoldings
