module

public import Unfoldings.Metric.Polygonal
public import Unfoldings.Metric.RouteLocal

/-! Intrinsic distances of polygonal regions depend locally only on their geometric germs. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s u : Set E}

/-- Local equality suffices to transfer distances if every potentially shorter route remains
inside the matching geometric neighborhood. Neither region needs to be convex. -/
theorem edist_le_of_local_eq {p : E} {r : ℝ}
    (local_eq : ∀ z, dist z p < r → (z ∈ s ↔ z ∈ u))
    (x y : PolygonalPoint s) (a b : PolygonalPoint u)
    (first : a.val = x.val) (last : b.val = y.val)
    (first_near : dist x.val p < r) (last_near : dist y.val p < r)
    (budget : edist x.val p + edist a b < ENNReal.ofReal r) : edist a b ≤ edist x y := by
  classical
  let f (z : PolygonalPoint s) : PolygonalPoint u :=
    if h : dist z.val p < r then ⟨z.val, (local_eq z.val h).mp z.property⟩ else a
  have at_x : f x = a := by
    apply PolygonalPoint.ext
    simp only [f, dite_eq_left first_near]
    exact first.symm
  have at_y : f y = b := by
    apply PolygonalPoint.ext
    simp only [f, dite_eq_left last_near]
    exact last.symm
  have progress (v w : PolygonalPoint s) :
      edist w.val p ≤ edist v.val p + stepCost v w := by
    calc
      _ ≤ edist w.val v.val + edist v.val p := edist_triangle _ _ _
      _ ≤ edist w v + edist v.val p :=
        add_le_add (ambient_edist_le_distance w v) le_rfl
      _ ≤ stepCost v w + edist v.val p := by
        rw [edist_comm w v]
        exact add_le_add (Route.distance_le_cost stepCost v w) le_rfl
      _ = _ := add_comm _ _
  have local_step (v w : PolygonalPoint s)
      (hv : edist v.val p < ENNReal.ofReal r) (hw : edist w.val p < ENNReal.ofReal r) :
      edist (f v) (f w) ≤ stepCost v w := by
    have near_v : dist v.val p < r := by
      rw [edist_dist] at hv
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp hv
    have near_w : dist w.val p < r := by
      rw [edist_dist] at hw
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp hw
    by_cases inside : segment ℝ v.val w.val ⊆ s
    · rw [stepCost, ite_eq_left inside]
      have all_near := (convex_ball p r).segment_subset near_v near_w
      have segment_inside : segment ℝ (f v).val (f w).val ⊆ u := by
        simp only [f, dite_eq_left near_v, dite_eq_left near_w]
        intro z member
        exact (local_eq z (all_near member)).mp (inside member)
      simpa only [f, dite_eq_left near_v, dite_eq_left near_w] using
        (edist_eq_of_segment segment_inside).le
    · simp only [stepCost, ite_eq_right inside, le_top]
  have bound := Route.map_edist_le_distance_of_radial_budget stepCost
    (fun z : PolygonalPoint s => edist z.val p) progress f (ENNReal.ofReal r) local_step x y
    (by rwa [at_x, at_y])
  rwa [at_x, at_y] at bound

/-- A locally matching star-shaped corner has the same intrinsic distances on a smaller ball.
This includes reentrant polygonal cones, with no convexity requirement. -/
theorem edist_eq_of_local_starConvex {p : E} {r : ℝ}
    (positive : 0 < r) (star : StarConvex ℝ p u) (center : p ∈ u)
    (local_eq : ∀ z, dist z p < r → (z ∈ s ↔ z ∈ u))
    (x y : PolygonalPoint s) (a b : PolygonalPoint u)
    (first : a.val = x.val) (last : b.val = y.val)
    (first_near : dist x.val p < r / 4) (last_near : dist y.val p < r / 4) :
    edist x y = edist a b := by
  have near_x : dist x.val p < r := by linarith
  have near_y : dist y.val p < r := by linarith
  let q : PolygonalPoint u := ⟨p, center⟩
  let c : PolygonalPoint s := ⟨p, (local_eq p (by simpa using positive)).mpr center⟩
  have segment_s (z : PolygonalPoint u) (near : dist z.val p < r) :
      segment ℝ p z.val ⊆ s := by
    have in_ball := (convex_ball p r).segment_subset
      (Metric.mem_ball_self positive) near
    intro w member
    exact (local_eq w (in_ball member)).mpr (star.segment_subset z.property member)
  have target_bound : edist a b ≤ edist x.val p + edist y.val p := by
    calc
      _ ≤ edist a q + edist q b := edist_triangle _ _ _
      _ = edist x.val p + edist y.val p := by
        rw [edist_comm a q, edist_eq_of_segment (star.segment_subset a.property),
          edist_eq_of_segment (star.segment_subset b.property)]
        simp only [q, first, last, edist_comm p]
  have source_bound : edist x y ≤ edist x.val p + edist y.val p := by
    calc
      _ ≤ edist x c + edist c y := edist_triangle _ _ _
      _ = edist x.val p + edist y.val p := by
        rw [edist_comm x c]
        have sx : segment ℝ c.val x.val ⊆ s := by
          simpa only [c, first] using segment_s a (by rwa [first])
        have sy : segment ℝ c.val y.val ⊆ s := by
          simpa only [c, last] using segment_s b (by rwa [last])
        rw [edist_eq_of_segment sx, edist_eq_of_segment sy]
        simp only [c, edist_comm p]
  have fits (d : ℝ≥0∞) (bound : d ≤ edist x.val p + edist y.val p) :
      edist x.val p + d < ENNReal.ofReal r := by
    calc
      _ ≤ edist x.val p + (edist x.val p + edist y.val p) := add_le_add le_rfl bound
      _ = ENNReal.ofReal (dist x.val p + (dist x.val p + dist y.val p)) := by
        simp only [edist_dist, ENNReal.ofReal_add dist_nonneg
          (add_nonneg dist_nonneg dist_nonneg), ENNReal.ofReal_add dist_nonneg dist_nonneg]
      _ < ENNReal.ofReal r :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (add_nonneg dist_nonneg (add_nonneg dist_nonneg dist_nonneg))).mpr (by linarith)
  apply le_antisymm
  · exact edist_le_of_local_eq (fun z hz => (local_eq z hz).symm) a b x y
      first.symm last.symm (by rwa [first]) (by rwa [last])
      (by simpa only [first] using fits (edist x y) source_bound)
  · exact edist_le_of_local_eq local_eq x y a b first last near_x near_y
      (fits (edist a b) target_bound)

/-- The whole intrinsic corner ball is determined by a locally equal star-shaped model.
The isometry preserves physical coordinates and applies to reentrant corners as well. -/
theorem exists_local_starConvex_ball_isometry (x : PolygonalPoint s) (a : PolygonalPoint u)
    (center : a.val = x.val) {r : ℝ} (positive : 0 < r)
    (star : StarConvex ℝ x.val u)
    (local_eq : ∀ z, dist z x.val < r → (z ∈ s ↔ z ∈ u)) :
    ∃ A : Metric.eball x (ENNReal.ofReal (r / 4)) ≃ᵢ
        Metric.eball a (ENNReal.ofReal (r / 4)),
      ∀ y, (A y).val.val = y.val.val := by
  have center_member : x.val ∈ u := center ▸ a.property
  have ambient_near {t : Set E} (z c : PolygonalPoint t)
      (near : edist z c < ENNReal.ofReal (r / 4)) : dist z.val c.val < r / 4 := by
    have bound := ambient_lipschitz.edist_le_mul z c
    simp only [ENNReal.coe_one, one_mul] at bound
    have small := bound.trans_lt near
    rw [edist_dist] at small
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp small
  have near_center : dist x.val x.val < r / 4 := by
    simpa only [dist_self] using div_pos positive (by norm_num : (0 : ℝ) < 4)
  let f (z : Metric.eball a (ENNReal.ofReal (r / 4))) : PolygonalPoint s := by
    have near : dist z.val.val x.val < r / 4 := by
      simpa only [center] using ambient_near z.val a z.property
    exact ⟨z.val.val, (local_eq z.val.val (by linarith)).mpr z.val.property⟩
  have near_f (z : Metric.eball a (ENNReal.ofReal (r / 4))) :
      dist (f z).val x.val < r / 4 := by
    simpa only [f, center] using ambient_near z.val a z.property
  have f_bound (z : Metric.eball a (ENNReal.ofReal (r / 4))) :
      edist (f z) x < ENNReal.ofReal (r / 4) := by
    rw [edist_eq_of_local_starConvex positive star center_member local_eq
      (f z) x z.val a rfl center (near_f z) near_center]
    exact z.property
  let g (z : Metric.eball a (ENNReal.ofReal (r / 4))) :
      Metric.eball x (ENNReal.ofReal (r / 4)) := ⟨f z, f_bound z⟩
  have isometric : Isometry g := by
    intro z w
    exact (edist_eq_of_local_starConvex positive star center_member local_eq
      (f z) (f w) z.val w.val rfl rfl (near_f z) (near_f w))
  have surjective : Function.Surjective g := by
    intro y
    have near : dist y.val.val x.val < r / 4 := ambient_near y.val x y.property
    let b : PolygonalPoint u :=
      ⟨y.val.val, (local_eq y.val.val (by linarith)).mp y.val.property⟩
    have b_near : edist b a < ENNReal.ofReal (r / 4) := by
      rw [← edist_eq_of_local_starConvex positive star center_member local_eq
        y.val x b a rfl center near near_center]
      exact y.property
    exact ⟨⟨b, b_near⟩, Subtype.ext (PolygonalPoint.ext rfl)⟩
  let B : Metric.eball a (ENNReal.ofReal (r / 4)) ≃ᵢ
      Metric.eball x (ENNReal.ofReal (r / 4)) :=
    ⟨Equiv.ofBijective g ⟨isometric.injective, surjective⟩, isometric⟩
  refine ⟨B.symm, ?_⟩
  intro y
  exact congrArg (fun z : Metric.eball x (ENNReal.ofReal (r / 4)) => z.val.val)
    (B.apply_symm_apply y)

end Unfoldings.PolygonalPoint
