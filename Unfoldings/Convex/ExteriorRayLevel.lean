module

public import Unfoldings.Convex.ExteriorPlan
public import Unfoldings.Convex.EnvelopeSublevels
public import Mathlib.Tactic.Module

/-! Truncate assigned exterior rays at a common physical height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (P : E.ExteriorPlan V)

/-- If the open rays avoid all their origins, the parallel rays are also
disjoint for distinct origins. -/
theorem pairwise_disjoint_openRays_of_avoids {S : Set Plane}
    (origins : ∀ v, P.point v ∈ S)
    (outside : ∀ v t, 0 < t → P.ray v t ∉ S) :
    Pairwise (fun v w => Disjoint (P.openRay v) (P.openRay w)) := by
  intro v w distinct
  by_cases directions : P.direction (P.slope v) = P.direction (P.slope w)
  · apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, first⟩ ⟨t, ht, last⟩
    have crossing := first.symm.trans last
    change P.point v + s • P.direction (P.slope v) =
      P.point w + t • P.direction (P.slope w) at crossing
    rw [← directions] at crossing
    rcases lt_trichotomy s t with before | same | after
    · have at_origin : P.point v = P.ray w (t - s) := by
        rw [ray, ← directions]
        calc
          _ = (P.point v + s • P.direction (P.slope v)) - s • P.direction (P.slope v) := by abel
          _ = _ := by rw [crossing]; module
      exact outside w _ (sub_pos.mpr before) (at_origin ▸ origins v)
    · rw [same] at crossing
      exact distinct (P.point_injective (add_right_cancel crossing))
    · have at_origin : P.point w = P.ray v (s - t) := by
        rw [ray]
        calc
          _ = (P.point w + t • P.direction (P.slope v)) - t • P.direction (P.slope v) := by abel
          _ = _ := by rw [← crossing]; module
      exact outside v _ (sub_pos.mpr after) (at_origin ▸ origins w)
  · exact P.open_rays_disjoint_of_direction_ne directions

variable (level : ℝ) (v : V)

/-- Travel time to the section height measured from an exterior ray's origin. -/
def timeAtLevel : ℝ := (level - E.height (P.point v)) / P.rate v

theorem timeAtLevel_pos (higher : E.height (P.point v) < level) :
    0 < P.timeAtLevel level v :=
  div_pos (sub_pos.mpr higher) (P.positive v)

def pointAtLevel : Plane := P.ray v (P.timeAtLevel level v)

theorem pointAtLevel_height (higher : E.height (P.point v) < level) :
    E.height (P.pointAtLevel level v) = level := by
  have rate_ne : P.rate v ≠ 0 := ne_of_gt (P.positive v)
  rw [pointAtLevel, P.height_ray v (P.timeAtLevel_pos level v higher).le,
    timeAtLevel, div_mul_cancel₀ _ rate_ne]
  ring

theorem pointAtLevel_mem_openRay (higher : E.height (P.point v) < level) :
    P.pointAtLevel level v ∈ P.openRay v :=
  ⟨_, P.timeAtLevel_pos level v higher, rfl⟩

theorem lineMap_pointAtLevel (t : ℝ) :
    AffineMap.lineMap (P.point v) (P.pointAtLevel level v) t =
      P.ray v (t * P.timeAtLevel level v) := by
  rw [pointAtLevel, AffineMap.lineMap_apply_module']
  dsimp [ray]
  module

theorem openSegment_pointAtLevel_subset_openRay (higher : E.height (P.point v) < level) :
    openSegment ℝ (P.point v) (P.pointAtLevel level v) ⊆ P.openRay v := by
  rw [openSegment_eq_image_lineMap]
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨_, mul_pos ht.1 (P.timeAtLevel_pos level v higher), P.lineMap_pointAtLevel level v t⟩

/-- The positive ray rate puts the truncated endpoint on the actual
frontier of the physical sublevel, even if the supporting plane changes. -/
theorem pointAtLevel_mem_frontier (higher : E.height (P.point v) < level) :
    P.pointAtLevel level v ∈ frontier {x | E.height x ≤ level} := by
  refine ⟨subset_closure (P.pointAtLevel_height level v higher).le, ?_⟩
  intro inside
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp isOpen_interior _ inside
  let t := P.timeAtLevel level v
  let y := P.ray v (t + ε / 2)
  have near : y ∈ Metric.ball (P.pointAtLevel level v) ε := by
    apply Metric.mem_ball.mpr
    have difference : y - P.pointAtLevel level v = (ε / 2) • P.direction (P.slope v) := by
      dsimp [y, t, pointAtLevel, ray]
      module
    rw [dist_eq_norm, difference, norm_smul, P.unit, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one]
    linarith only [positive]
  have after : 0 < t + ε / 2 := by
    exact add_pos (P.timeAtLevel_pos level v higher) (by positivity)
  have y_height : E.height y = level + (ε / 2) * P.rate v := by
    dsimp only [y]
    rw [P.height_ray v after.le, add_mul, ← add_assoc,
      ← P.height_ray v (P.timeAtLevel_pos level v higher).le]
    exact congrArg (fun x : ℝ => x + ε / 2 * P.rate v) (P.pointAtLevel_height level v higher)
  have above : level < E.height y := by
    rw [y_height]
    exact lt_add_of_pos_right _ (mul_pos (by positivity) (P.positive v))
  have inside_sublevel : y ∈ {x | E.height x ≤ level} := interior_subset (ball near)
  exact above.not_ge inside_sublevel

end Unfoldings.SlopeEnvelope.ExteriorPlan
