module

public import Unfoldings.Roof.GermSupports
public import Unfoldings.Roof.ProjectedFlatness
public import Unfoldings.Geometry.ConeBoundaryRays

/-! A sign change in an actual incident face meets the supported cone boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {v : C.Vertex Set.univ}

theorem exists_germ_crossing_point (n : Space) (upward : 0 < n 2)
    (p : C.LinkGerm Set.univ v)
    (crossing : inner ℝ n (K.folding.germDirection p.val) *
      inner ℝ n (K.folding.germDirection (C.linkTurn Set.univ v p).val) < 0) :
    ∃ q : Plane, q ≠ 0 ∧ q ∈ strictRayCone (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ v p)) ∧
      (∀ a : C.CornerAt Set.univ v, 0 ≤ K.germUpperForm v n a q) ∧
      K.germUpperForm v n ⟨p.val.1, p.property⟩ q = 0 := by
  let x := inner ℝ n (K.folding.germDirection p.val)
  let y := inner ℝ n (K.folding.germDirection (C.linkTurn Set.univ v p).val)
  have weights : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * x + b * y = 0 := by
    rcases mul_neg_iff.mp crossing with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨-y, x, neg_pos.mpr hy, hx, by ring⟩
    · exact ⟨y, -x, hy, neg_pos.mpr hx, by ring⟩
  obtain ⟨a, b, ha, hb, balance⟩ := weights
  let q := a • K.projectedGermRay p + b • K.projectedGermRay (C.linkTurn Set.univ v p)
  have member : q ∈ strictRayCone (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ v p)) := ⟨a, ha, b, hb, rfl⟩
  refine ⟨q, ?_, member, ?_, ?_⟩
  · intro zero
    rw [zero] at member
    exact zero_not_mem_strictRayCone (K.projectedGermRay_orient_ne_zero p) member
  · intro c
    have left := mul_le_mul_of_nonneg_left (K.germUpperForm_bound n upward c p) ha.le
    have right := mul_le_mul_of_nonneg_left
      (K.germUpperForm_bound n upward c (C.linkTurn Set.univ v p)) hb.le
    change 0 ≤ K.germUpperForm v n c (a • _ + b • _)
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change a * x + b * y = 0 at balance
    dsimp [x, y] at balance
    linarith
  · have own := K.germUpperForm_own n p
    have turn := K.germUpperForm_own n (C.linkTurn Set.univ v p)
    change K.germUpperForm v n ⟨p.val.1, p.property⟩
      (K.projectedGermRay (C.linkTurn Set.univ v p)) = _ at turn
    change K.germUpperForm v n ⟨p.val.1, p.property⟩ (a • _ + b • _) = 0
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, own, turn]
    exact balance

end Unfoldings.ConvexRoof
