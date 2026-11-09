module

public import Unfoldings.Cone.AngularChord
public import Unfoldings.Cone.HeadingSector

/-!
# Shortcuts across a bounded heading interval

A pointed sector between real headings inside the fan is covered by its
closed pieces. Its chord therefore lifts with exact length, even when the
whole fan is reentrant. This gives strict apex shortcuts across multiple
original pieces.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem headingSector_subset_faces (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle) :
    headingSector a b ⊆ ⋃ i, A.faceImage i := by
  intro z inside
  obtain ⟨r, θ, bounds, equal⟩ := (mem_headingSector_iff_polar a b positive small z).mp inside
  obtain ⟨i, interval⟩ := A.exists_closed_heading_piece θ
    ⟨first.trans bounds.1, bounds.2.trans last⟩
  exact Set.mem_iUnion.mpr ⟨i, (A.mem_faceImage_iff i z).mpr ⟨r, θ, interval, equal⟩⟩

theorem dist_eq_of_mem_headingSector (full_bound : A.totalAngle < 2 * Real.pi)
    (a b : ℝ) (positive : 0 < b - a) (small : b - a < Real.pi)
    (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    {x y : A.Surface} (left : A.develop x ∈ headingSector a b)
    (right : A.develop y ∈ headingSector a b) :
    dist x y = dist (A.develop x) (A.develop y) :=
  A.dist_eq_of_segment_subset full_bound x y
    (((convex_headingSector a b).segment_subset left right).trans
      (A.headingSector_subset_faces a b positive small first last))

/-- An angular span of less than pi gives a strict intrinsic shortcut.
The whole fan may have angle greater than pi. -/
theorem dist_lt_via_origin_of_mem_headingSector (full_bound : A.totalAngle < 2 * Real.pi)
    (a b : ℝ) (positive : 0 < b - a) (small : b - a < Real.pi)
    (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    {x y : A.Surface} (left : A.develop x ∈ headingSector a b)
    (right : A.develop y ∈ headingSector a b)
    (left_nonzero : x ≠ A.origin) (right_nonzero : y ≠ A.origin) :
    dist x y < dist x A.origin + dist A.origin y := by
  have nonzero (z : A.Surface) (hz : z ≠ A.origin) : A.develop z ≠ 0 := by
    intro zero
    exact hz (A.develop_injective_of_lt_full full_bound (zero.trans A.develop_origin.symm))
  have strict := dist_lt_via_zero_of_mem_headingSector a b positive small left right
    (nonzero x left_nonzero) (nonzero y right_nonzero)
  rw [A.dist_eq_of_mem_headingSector full_bound a b positive small first last left right]
  simpa only [dist_zero_right, dist_zero_left, A.norm_develop, dist_comm] using strict

end Unfoldings.AngularFan
