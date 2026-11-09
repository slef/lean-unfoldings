module

public import Unfoldings.Cone.SectorClosed
public import Unfoldings.Cone.SectorShortcut
public import Mathlib.Analysis.Complex.Isometry

/-!
# Sectors with arbitrary real heading bounds

Rotating a pointed sector retains convexity and its strict radial shortcut.
Closed real heading coordinates keep track of which copy of a ray is meant,
without reducing headings modulo a full turn.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings

def headingSector (a b : ℝ) : Set ℂ :=
  rotation (Circle.exp a) '' planarSector (b - a)

theorem convex_headingSector (a b : ℝ) : Convex ℝ (headingSector a b) :=
  (convex_planarSector (b - a)).linear_image (rotation (Circle.exp a)).toLinearMap

theorem mem_headingSector_iff_polar (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (z : ℂ) :
    z ∈ headingSector a b ↔
      ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc a b, z = (r : ℂ) * polarRay θ := by
  constructor
  · rintro ⟨w, inside, rfl⟩
    obtain ⟨r, θ, bounds, rfl⟩ :=
      (mem_planarSector_iff_polar (b - a) positive small w).mp inside
    refine ⟨r, a + θ, ⟨by linarith [bounds.1], by linarith [bounds.2]⟩, ?_⟩
    change polarRay a * ((r : ℂ) * polarRay θ) = (r : ℂ) * polarRay (a + θ)
    rw [polarRay_add]
    ring
  · rintro ⟨r, θ, bounds, rfl⟩
    refine ⟨(r : ℂ) * polarRay (θ - a),
      polar_mem_planarSector (b - a) r (θ - a) positive small r.coe_nonneg
        ⟨by linarith [bounds.1], by linarith [bounds.2]⟩, ?_⟩
    change polarRay a * ((r : ℂ) * polarRay (θ - a)) = (r : ℂ) * polarRay θ
    calc
      _ = (r : ℂ) * (polarRay a * polarRay (θ - a)) := by ring
      _ = _ := by rw [← polarRay_add, add_sub_cancel]

theorem dist_lt_via_zero_of_mem_headingSector (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) {z w : ℂ}
    (left : z ∈ headingSector a b) (right : w ∈ headingSector a b)
    (left_nonzero : z ≠ 0) (right_nonzero : w ≠ 0) :
    dist z w < dist z 0 + dist 0 w := by
  obtain ⟨x, hx, rfl⟩ := left
  obtain ⟨y, hy, rfl⟩ := right
  let R := rotation (Circle.exp a)
  have x_nonzero : x ≠ 0 := by
    intro zero
    exact left_nonzero (by change R x = 0; rw [zero, map_zero])
  have y_nonzero : y ≠ 0 := by
    intro zero
    exact right_nonzero (by change R y = 0; rw [zero, map_zero])
  have strict := dist_lt_via_zero_of_mem_planarSector (b - a)
    (Real.sin_pos_of_pos_of_lt_pi positive small) hx hy x_nonzero y_nonzero
  change dist (R x) (R y) < dist (R x) 0 + dist 0 (R y)
  rw [← R.map_zero, R.isometry.dist_eq, R.isometry.dist_eq, R.isometry.dist_eq]
  exact strict

end Unfoldings
