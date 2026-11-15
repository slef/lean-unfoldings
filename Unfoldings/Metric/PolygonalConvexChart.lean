module

public import Unfoldings.Metric.Polygonal
public import Mathlib.Topology.MetricSpace.Isometry

/-! Exact intrinsic whole-ball charts from local equality with an actual convex region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s u : Set E}

/-- A local convex geometric patch forbids every intrinsic shortcut between its ball points. -/
theorem edist_eq_of_local_convex {p : E} {r : ℝ} (convex : Convex ℝ u)
    (local_eq : ∀ z, dist z p < r → (z ∈ s ↔ z ∈ u))
    (x y : PolygonalPoint s) (first : dist x.val p < r) (last : dist y.val p < r) :
    edist x y = edist x.val y.val := by
  apply edist_eq_of_segment
  have in_u := convex.segment_subset ((local_eq x.val first).mp x.property)
    ((local_eq y.val last).mp y.property)
  have in_ball := (convex_ball p r).segment_subset (Metric.mem_ball.mpr first)
    (Metric.mem_ball.mpr last)
  intro z member
  exact (local_eq z (Metric.mem_ball.mp (in_ball member))).mpr (in_u member)

/-- Local geometric equality gives a whole intrinsic ball isometric to the actual convex patch.
The chart preserves every physical point and the exact supplied radius. -/
theorem exists_local_convex_ball_isometry (x : PolygonalPoint s) (a : u)
    (center : a.val = x.val) {r : ℝ} (positive : 0 < r) (convex : Convex ℝ u)
    (local_eq : ∀ z, dist z x.val < r → (z ∈ s ↔ z ∈ u)) :
    ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ Metric.ball a r,
      ∀ y, (A y).val.val = y.val.val := by
  have center_near : dist x.val x.val < r := by simpa only [dist_self] using positive
  let f (z : Metric.ball a r) : PolygonalPoint s := by
    have close : dist z.val.val x.val < r := by
      simpa only [Subtype.dist_eq, center] using (Metric.mem_ball.mp z.property)
    exact ⟨z.val.val, (local_eq z.val.val close).mpr z.val.property⟩
  have near (z : Metric.ball a r) : dist (f z).val x.val < r := by
    simpa only [f, Subtype.dist_eq, center] using (Metric.mem_ball.mp z.property)
  have isometric : Isometry f := by
    intro z w
    exact edist_eq_of_local_convex convex local_eq (f z) (f w) (near z) (near w)
  have intrinsic_near (z : Metric.ball a r) : edist (f z) x < ENNReal.ofReal r := by
    rw [edist_eq_of_local_convex convex local_eq (f z) x (near z) center_near, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr (near z)
  let g (z : Metric.ball a r) : Metric.eball x (ENNReal.ofReal r) := ⟨f z, intrinsic_near z⟩
  have isometric_g : Isometry g := fun z w => isometric z w
  have surjective_g : Function.Surjective g := by
    intro y
    have ambient : edist y.val.val x.val < ENNReal.ofReal r := by
      have bound := ambient_lipschitz.edist_le_mul y.val x
      simp only [ENNReal.coe_one, one_mul] at bound
      exact bound.trans_lt y.property
    have close : dist y.val.val x.val < r := by
      rw [edist_dist] at ambient
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp ambient
    let z : Metric.ball a r := ⟨⟨y.val.val, (local_eq y.val.val close).mp y.val.property⟩, by
      change dist y.val.val a.val < r
      rwa [center]⟩
    exact ⟨z, Subtype.ext (PolygonalPoint.ext rfl)⟩
  let B : Metric.ball a r ≃ᵢ Metric.eball x (ENNReal.ofReal r) :=
    ⟨Equiv.ofBijective g ⟨isometric_g.injective, surjective_g⟩, isometric_g⟩
  refine ⟨B.symm, ?_⟩
  intro y
  have same := congrArg (fun z : Metric.eball x (ENNReal.ofReal r) => z.val.val)
    (B.apply_symm_apply y)
  exact same

end Unfoldings.PolygonalPoint
