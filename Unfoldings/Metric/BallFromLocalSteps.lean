module

public import Unfoldings.Metric.LocalMap
public import Unfoldings.Metric.BallIsometry
public import Unfoldings.Metric.HalfPlaneFilling

/-! A geometric filling and local route-step estimates construct a whole metric-ball chart. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I : Type*} (E : I → Type*) [∀ i, PseudoEMetricSpace (E i)]
  (glue : Total E → Total E → Prop) {Y : Type*} [MetricSpace Y]

/-- A nonexpanding geometric filling of a model ball is isometric when original
representatives satisfy local route-step estimates. Coverage concerns the whole actual
ball; no isometry or final development is assumed in the geometric filling. -/
theorem ball_isometry_of_local_steps (a : Total E) (y : Y) {r : ℝ} (positive : 0 < r)
    (coordinates : Total E → Y)
    (local_step : ∀ b c,
      edist (point E glue a) (point E glue b) < ENNReal.ofReal (4 * r) →
      edist (point E glue a) (point E glue c) < ENNReal.ofReal (4 * r) →
      edist (coordinates b) (coordinates c) ≤ stepCost E glue b c)
    (fill : Metric.ball y r → Realization E glue) (nonexpanding : LipschitzWith 1 fill)
    (center : fill ⟨y, Metric.mem_ball_self positive⟩ = point E glue a)
    (representatives : ∀ z, ∃ b, point E glue b = fill z ∧ coordinates b = z.val)
    (cover : ∀ x ∈ Metric.eball (point E glue a) (ENNReal.ofReal r), ∃ z, fill z = x) :
    ∃ A : Metric.ball y r ≃ᵢ Metric.eball (point E glue a) (ENNReal.ofReal r),
      ∀ z, (A z).val = fill z := by
  have bound (z : Metric.ball y r) :
      edist (fill z) (point E glue a) ≤ edist z.val y := by
    have estimate := nonexpanding.edist_le_mul z ⟨y, Metric.mem_ball_self positive⟩
    simpa only [center, ENNReal.coe_one, one_mul, Subtype.edist_eq] using estimate
  have near (z : Metric.ball y r) : edist z.val y < ENNReal.ofReal r := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr z.property
  let f (z : Metric.ball y r) : Metric.eball (point E glue a) (ENNReal.ofReal r) :=
    ⟨fill z, (bound z).trans_lt (near z)⟩
  have isometric : Isometry f := by
    intro z w
    obtain ⟨b, first, first_coordinates⟩ := representatives z
    obtain ⟨c, last, last_coordinates⟩ := representatives w
    have budget : edist (point E glue a) (point E glue b) +
        edist (coordinates b) (coordinates c) < ENNReal.ofReal (4 * r) := by
      have root := bound z
      have triangle := edist_triangle z.val y w.val
      rw [edist_comm y w.val] at triangle
      rw [first, edist_comm, first_coordinates, last_coordinates]
      calc
        _ ≤ edist z.val y + (edist z.val y + edist w.val y) :=
          add_le_add root triangle
        _ = ENNReal.ofReal (dist z.val y + (dist z.val y + dist w.val y)) := by
          simp only [edist_dist,
            ENNReal.ofReal_add dist_nonneg (add_nonneg dist_nonneg dist_nonneg),
            ENNReal.ofReal_add dist_nonneg dist_nonneg]
        _ < ENNReal.ofReal (4 * r) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
            (add_nonneg dist_nonneg (add_nonneg dist_nonneg dist_nonneg))).mpr
              (by
                have hz : dist z.val y < r := z.property
                have hw : dist w.val y < r := w.property
                linarith)
    have lower := map_edist_le_edist_of_budget E glue coordinates (point E glue a)
      (ENNReal.ofReal (4 * r)) local_step b c budget
    rw [first, last, first_coordinates, last_coordinates] at lower
    exact le_antisymm (nonexpanding.edist_le_mul z w |>.trans_eq (one_mul _)) lower
  have onto : Function.Surjective f := by
    intro x
    obtain ⟨z, equal⟩ := cover x.val x.property
    exact ⟨z, Subtype.ext equal⟩
  exact ⟨⟨Equiv.ofBijective f ⟨isometric.injective, onto⟩, isometric⟩, fun _ => rfl⟩

/-- Two nonexpanding original half-disk fillings, with actual representatives and whole-ball
coverage, construct the planar chart once local seam steps respect their coordinates. -/
theorem halfPlane_ball_isometry_of_local_steps (a : Total E) {r : ℝ} (positive : 0 < r)
    (coordinates : Total E → ℂ)
    (local_step : ∀ b c,
      edist (point E glue a) (point E glue b) < ENNReal.ofReal (4 * r) →
      edist (point E glue a) (point E glue c) < ENNReal.ofReal (4 * r) →
      edist (coordinates b) (coordinates c) ≤ stepCost E glue b c)
    (fill : Metric.ball (0 : ℂ) r → Realization E glue)
    (upper : LipschitzOnWith 1 fill {z | 0 ≤ z.val.im})
    (lower : LipschitzOnWith 1 fill {z | z.val.im ≤ 0})
    (center : fill ⟨0, Metric.mem_ball_self positive⟩ = point E glue a)
    (representatives : ∀ z, ∃ b, point E glue b = fill z ∧ coordinates b = z.val)
    (cover : ∀ x ∈ Metric.eball (point E glue a) (ENNReal.ofReal r), ∃ z, fill z = x) :
    ∃ A : Metric.ball (0 : ℂ) r ≃ᵢ Metric.eball (point E glue a) (ENNReal.ofReal r),
      ∀ z, (A z).val = fill z :=
  ball_isometry_of_local_steps E glue a 0 positive coordinates local_step fill
    (halfPlane_filling_lipschitz fill upper lower) center representatives cover

end Unfoldings.MetricGluing
