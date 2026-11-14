module

public import Unfoldings.Convex.ExteriorContacts

/-! First-contact truncation makes all retained exterior ray pieces geometrically disjoint. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V)

/-- A shared point on parallel positive rays orders their origins along that same line. -/
theorem parallel_crossing_contact {v w : V} {s t : ℝ}
    (same : R.direction (R.slope v) = R.direction (R.slope w))
    (tpos : 0 < t) (ordered : t < s) (crossing : R.ray v s = R.ray w t) :
    R.Contact v w ∧ E.height (R.point w) < E.height (R.ray v s) := by
  have equality : R.point w = R.ray v (s - t) := by
    change R.point w = R.point v + (s - t) • R.direction (R.slope v)
    have cross : R.point v + s • R.direction (R.slope v) =
        R.point w + t • R.direction (R.slope v) := by
      simpa only [ray, ← same] using crossing
    calc
      R.point w = (R.point w + t • R.direction (R.slope v)) -
        t • R.direction (R.slope v) := by abel
      _ = (R.point v + s • R.direction (R.slope v)) -
        t • R.direction (R.slope v) := by rw [cross]
      _ = R.point v + (s - t) • R.direction (R.slope v) := by rw [sub_smul]; abel
  refine ⟨⟨s - t, sub_pos.mpr ordered, equality⟩, ?_⟩
  rw [equality, R.height_ray v (sub_nonneg.mpr ordered.le), R.height_ray v (by linarith)]
  have rate : 0 < R.rate v := R.positive v
  nlinarith

/-- Distinct roots have disjoint retained open pieces, even when their full rays coincide.
Endpoints may meet a root and then follow that root's independently assigned continuation. -/
theorem openPieces_pairwise_disjoint :
    Pairwise (fun v w => Disjoint (R.openPiece v) (R.openPiece w)) := by
  intro v w different
  by_cases directions : R.direction (R.slope v) = R.direction (R.slope w)
  · apply Set.disjoint_left.mpr
    rintro x ⟨s, spos, first, before_v⟩ ⟨t, tpos, last, before_w⟩
    have crossing : R.ray v s = R.ray w t := first.symm.trans last
    rcases lt_trichotomy s t with ordered | equal | ordered
    · obtain ⟨contact, below⟩ :=
        R.parallel_crossing_contact directions.symm spos ordered crossing.symm
      have above := before_w v contact
      rw [last] at above
      exact lt_asymm above below
    · have same_points : R.point v = R.point w := by
        have cross : R.point v + s • R.direction (R.slope v) =
            R.point w + s • R.direction (R.slope v) := by
          simpa only [ray, ← directions, ← equal] using crossing
        exact add_right_cancel cross
      exact different (R.point_injective same_points)
    · obtain ⟨contact, below⟩ := R.parallel_crossing_contact directions tpos ordered crossing
      have above := before_v w contact
      rw [first] at above
      exact lt_asymm above below
  · exact (R.open_rays_disjoint_of_direction_ne directions).mono
      (R.openPiece_subset_openRay v) (R.openPiece_subset_openRay w)

end Unfoldings.SlopeEnvelope.ExteriorPlan
