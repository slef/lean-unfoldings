module

public import Unfoldings.Cap.SectionFrame
public import Unfoldings.Cap.SectionInteriors
public import Unfoldings.Cap.ProjectedSeamUnique

/-!
# Isolating the actual original seam between adjacent section samples

No original seam meets either open face piece. A seam meeting the interval
between two adjacent interior samples is therefore the actual transition seam.
When the face labels agree, the whole interval is interior and no seam meets it.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Ordered parameters on one affine line give a segment between its endpoint parameters. -/
theorem lineMap_mem_segment_of_parameters (p q : Plane) {a b r : ℝ}
    (ordered : a ≤ b) (lower : a ≤ r) (upper : r ≤ b) :
    AffineMap.lineMap p q r ∈ segment ℝ (AffineMap.lineMap p q a) (AffineMap.lineMap p q b) := by
  rw [← image_segment ℝ (AffineMap.lineMap p q) a b]
  exact ⟨r, (segment_eq_Icc ordered).symm ▸ ⟨lower, upper⟩, rfl⟩

namespace ConvexCap.SectionFaceTrace

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)

/-- Any seam meeting the interval between adjacent samples is the actual transition seam. -/
theorem seam_between_samples_eq_transition (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (s : C.Seam)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (other : C.Seam) {r : ℝ} (lower : T.middleTime i.castSucc < r)
    (upper : r < T.middleTime i.succ)
    (member : AffineMap.lineMap p q r ∈
      (K.projectedTriangle (C.left other).face).edge (C.left other).edge) : other = s := by
  rcases lt_trichotomy r (T.time i.castSucc.succ : ℝ) with before | equal | after
  · have inside := T.point_interior_of_time_between different regular i.castSucc
      ((T.middleTime_between i.castSucc).1.trans lower) before
    exact (K.projected_seam_not_mem_face_interior other _ inside member).elim
  · rw [equal] at member
    exact K.projected_seam_unique_at_regular_point other s member crossing
      (regular (T.time i.castSucc.succ))
  · have start : (T.time i.succ.castSucc : ℝ) < r := by
      simpa only [Fin.succ_castSucc] using after
    have inside := T.point_interior_of_time_between different regular i.succ start
      (upper.trans (T.middleTime_between i.succ).2)
    exact (K.projected_seam_not_mem_face_interior other _ inside member).elim

/-- Repeated original face labels leave the entire interval between samples in that interior. -/
theorem between_samples_interior_of_same_face (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (same : T.face i.castSucc = T.face i.succ) {r : ℝ}
    (lower : T.middleTime i.castSucc ≤ r) (upper : r ≤ T.middleTime i.succ) :
    AffineMap.lineMap p q r ∈ interior (K.projectedTriangle (T.face i.castSucc)).carrier := by
  have ordered : T.middleTime i.castSucc ≤ T.middleTime i.succ :=
    (T.middleTime_increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
  have between := lineMap_mem_segment_of_parameters p q ordered lower upper
  rw [← T.middlePoint_eq_section, ← T.middlePoint_eq_section] at between
  have first := T.middlePoint_interior different regular i.castSucc
  have last := T.middlePoint_interior different regular i.succ
  rw [← same] at last
  exact (K.projectedTriangle (T.face i.castSucc)).convex_carrier.interior.segment_subset
    first last between

/-- No original seam lies between adjacent samples with the same original face label. -/
theorem seam_avoids_between_samples_of_same_face (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (same : T.face i.castSucc = T.face i.succ) {r : ℝ}
    (lower : T.middleTime i.castSucc ≤ r) (upper : r ≤ T.middleTime i.succ) (s : C.Seam) :
    AffineMap.lineMap p q r ∉ (K.projectedTriangle (C.left s).face).edge (C.left s).edge :=
  K.projected_seam_not_mem_face_interior s _
    (T.between_samples_interior_of_same_face different regular i same lower upper)

end ConvexCap.SectionFaceTrace
end Unfoldings
