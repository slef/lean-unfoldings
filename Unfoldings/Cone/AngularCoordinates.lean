module

public import Unfoldings.Cone.AngularOverlap
public import Unfoldings.Cone.SectorClosed
public import Unfoldings.Cone.AngularMetric

/-!
# Closed heading intervals and full-turn coverage

Closed rigid sector images retain their banks and apex. Every heading in the
total interval lies in a closed piece. A full-turn angular development
therefore covers the whole Euclidean plane.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem place_start (i : Fin (n + 1)) (r : ℝ≥0) :
    A.place i (A.start i r) = (r : ℂ) * polarRay (A.heading i.castSucc) := by
  change polarRay (A.heading i.castSucc) * (r : ℂ) = _
  ring

theorem place_finish (i : Fin (n + 1)) (r : ℝ≥0) :
    A.place i (A.finish i r) = (r : ℂ) * polarRay (A.heading i.succ) := by
  change polarRay (A.heading i.castSucc) * ((r : ℝ) • polarRay (A.angle i)) = _
  rw [A.heading_succ, polarRay_add, Complex.real_smul]
  ring

theorem norm_place (i : Fin (n + 1)) (x : A.Cell i) : ‖A.place i x‖ = ‖x.val‖ := by
  simp [place]

theorem mem_faceImage_iff (i : Fin (n + 1)) (z : ℂ) :
    z ∈ A.faceImage i ↔
      ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ),
        z = (r : ℂ) * polarRay θ := by
  constructor
  · rintro ⟨w, inside, mapped⟩
    obtain ⟨r, θ, bounds, rfl⟩ := (mem_planarSector_iff_polar
      (A.angle i) (A.positive i) (A.small i) w).mp inside
    refine ⟨r, A.heading i.castSucc + θ, ?_, ?_⟩
    · rw [A.heading_succ]
      constructor <;> linarith [bounds.1, bounds.2]
    · change polarRay (A.heading i.castSucc) * ((r : ℂ) * polarRay θ) = z at mapped
      rw [← mapped, polarRay_add]
      ring
  · rintro ⟨r, θ, bounds, rfl⟩
    have local_heading : θ - A.heading i.castSucc ∈ Set.Icc 0 (A.angle i) := by
      rw [A.heading_succ] at bounds
      constructor <;> linarith [bounds.1, bounds.2]
    refine ⟨(r : ℂ) * polarRay (θ - A.heading i.castSucc),
      polar_mem_planarSector (A.angle i) r _ (A.positive i) (A.small i)
        r.coe_nonneg local_heading, ?_⟩
    change polarRay (A.heading i.castSucc) * ((r : ℂ) *
      polarRay (θ - A.heading i.castSucc)) = (r : ℂ) * polarRay θ
    calc
      _ = (r : ℂ) * (polarRay (A.heading i.castSucc) *
          polarRay (θ - A.heading i.castSucc)) := by ring
      _ = _ := by rw [← polarRay_add, add_sub_cancel]

theorem exists_closed_heading_piece (θ : ℝ) (inside : θ ∈ Set.Icc 0 A.totalAngle) :
    ∃ i : Fin (n + 1), θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ) := by
  classical
  by_cases bank : θ ∈ Set.range A.heading
  · obtain ⟨k, rfl⟩ := bank
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · exact ⟨i, le_rfl, A.heading_strictMono.monotone Fin.castSucc_lt_succ.le⟩
    · refine ⟨Fin.last n, A.heading_strictMono.monotone (Fin.le_last _), ?_⟩
      rw [Fin.succ_last]
  · have off (k) : θ ≠ A.heading k := fun equal => bank ⟨k, equal.symm⟩
    have first : θ ≠ 0 := by simpa only [A.heading_zero] using off 0
    have last : θ ≠ A.totalAngle := by
      simpa only [A.heading_last] using off (Fin.last (n + 1))
    obtain ⟨i, bounds⟩ := A.exists_heading_piece θ
      ⟨lt_of_le_of_ne inside.1 first.symm, lt_of_le_of_ne inside.2 last⟩ off
    exact ⟨i, bounds.1.le, bounds.2.le⟩

theorem faceImage_cover_of_full (full : A.totalAngle = 2 * Real.pi) :
    (⋃ i, A.faceImage i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨r, θ, heading, equal⟩ := exists_polar_nonnegative_heading z
  rw [← full] at heading
  obtain ⟨i, bounds⟩ := A.exists_closed_heading_piece θ heading
  exact Set.mem_iUnion.mpr ⟨i, (A.mem_faceImage_iff i z).mpr ⟨r, θ, bounds, equal⟩⟩

theorem exists_face_lift_of_full (full : A.totalAngle = 2 * Real.pi) (z : ℂ) :
    ∃ i, ∃ x : A.Cell i, A.place i x = z := by
  have covered : z ∈ ⋃ i, A.faceImage i := by rw [A.faceImage_cover_of_full full]; trivial
  obtain ⟨i, w, inside, equal⟩ := Set.mem_iUnion.mp covered
  exact ⟨i, ⟨w, inside⟩, equal⟩

theorem develop_surjective_of_full (full : A.totalAngle = 2 * Real.pi) :
    Function.Surjective A.develop := by
  intro z
  obtain ⟨i, x, equal⟩ := A.exists_face_lift_of_full full z
  exact ⟨A.faceMap i x, (A.develop_faceMap i x).trans equal⟩

theorem norm_develop (z : A.Surface) : ‖A.develop z‖ = dist A.origin z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue z
  change ‖A.develop (A.faceMap i x)‖ = dist A.origin (A.faceMap i x)
  rw [A.develop_faceMap]
  exact (A.norm_place i x).trans (A.dist_origin_faceMap i x).symm

end Unfoldings.AngularFan
