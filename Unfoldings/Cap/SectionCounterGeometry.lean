module

public import Unfoldings.Cap.ParentRayCounter
public import Unfoldings.Cap.ParentSectionPhase
public import Unfoldings.Cap.SectionCrossingIsolation

/-!
# Actual counter changes at the unique original section transition

Every nonzero parent-ray counter change between adjacent interior samples comes
from the actual transition seam. At that selected seam, multiplying its exact
counter change by descendant curvature gives the actual signed bank phase.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- A nonzero actual parent-counter change identifies the unique actual transition seam. -/
theorem parent_counter_change_eq_transition {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (s : C.Seam)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (changes : M.parentSectionCounter p q (T.middleTime i.succ) e.val -
      M.parentSectionCounter p q (T.middleTime i.castSucc) e.val ≠ 0) :
    M.selection.edge e = s := by
  have ordered : T.middleTime i.castSucc ≤ T.middleTime i.succ :=
    (T.middleTime_increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
  obtain ⟨r, lower, upper, member⟩ := sectionRayCounter_change_meets different ordered changes
  rw [M.parent_segment_eq_original_seam e] at member
  have strict_upper : r < T.middleTime i.succ := lt_of_le_of_ne upper (by
    intro equal
    rw [equal, ← T.middlePoint_eq_section] at member
    exact K.projected_seam_not_mem_face_interior (M.selection.edge e) _
      (T.middlePoint_interior different regular i.succ) member)
  exact T.seam_between_samples_eq_transition different regular i s crossing
    (M.selection.edge e) lower strict_upper member

/-- Repeated original face labels leave every actual parent-ray counter unchanged. -/
theorem parent_counter_change_zero_of_same_face {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (same : T.face i.castSucc = T.face i.succ)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    M.parentSectionCounter p q (T.middleTime i.succ) e.val -
      M.parentSectionCounter p q (T.middleTime i.castSucc) e.val = 0 := by
  by_contra changes
  have ordered : T.middleTime i.castSucc ≤ T.middleTime i.succ :=
    (T.middleTime_increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
  obtain ⟨r, lower, upper, member⟩ := sectionRayCounter_change_meets different ordered changes
  rw [M.parent_segment_eq_original_seam e] at member
  exact T.seam_avoids_between_samples_of_same_face different regular i same lower.le upper
    (M.selection.edge e) member

/-- The unique selected transition's signed counter contributes exactly its actual bank phase. -/
theorem parent_counter_change_mul_curvature {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
        (C.left (M.selection.edge e)).edge) :
    (M.parentSectionCounter p q (T.middleTime i.succ) e.val -
      M.parentSectionCounter p q (T.middleTime i.castSucc) e.val) * M.subtreeCurvature e.val =
        M.parentSectionPhase e.val (q - p) := by
  have member : AffineMap.lineMap p q (T.time i.castSucc.succ : ℝ) ∈
      segment ℝ (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val)) := by
    rw [M.parent_segment_eq_original_seam e]
    exact crossing
  have upper : (T.time i.castSucc.succ : ℝ) < T.middleTime i.succ := by
    simpa only [Fin.succ_castSucc] using (T.middleTime_between i.succ).1
  have change := sectionRayCounter_change_at_crossing different
    (K.projectedVertex_off_section_axis different regular e.val)
    (K.projectedVertex_off_section_axis different regular (M.parents.parent e.val))
    (T.middleTime_between i.castSucc).2 upper member
  change (sectionRayCounter p q (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val)) (T.middleTime i.succ) -
    sectionRayCounter p q (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val)) (T.middleTime i.castSucc)) * _ = _
  rw [change]
  unfold parentSectionPhase
  split_ifs <;> ring

end Unfoldings.ConvexCap.SectorForest
