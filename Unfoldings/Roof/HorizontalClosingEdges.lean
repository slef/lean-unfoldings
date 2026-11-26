module

public import Unfoldings.Roof.HorizontalClosingContacts
public import Unfoldings.Roof.ProjectedGermSegments
public import Unfoldings.Roof.OriginalFaceHeight

/-! Each adjacent pair of horizontal contact vertices determines one supported edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.RegularClosingLink

open Cap InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {U : Set Face} {origin : Plane} {I : Type*}

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

variable (L : K.RegularClosingLink U origin east I)

open Classical in
/-- Lift an incident restricted germ back to its actual refined face. -/
theorem exists_contactGerm (i : I) (side : Bool) :
    let rate := if side then L.incoming i else L.outgoing i
    ∃ g : C.Germ, g.1.1 = L.contactFace i side ∧
      K.projectedGermStart g = origin + L.time i • east ∧
      K.projectedGermFinish g = origin + (L.time i + rate) • east := by
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let e := L.bank i
  let q : R.BoundaryEnd Set.univ := if side then R.boundaryMate Set.univ e else e
  let g : C.Germ := ((q.val.1.1.val, q.val.1.2), q.val.2)
  have start : K.projectedGermStart g = Cap.horizontal (F.boundaryPosition q) := by
    rw [F.boundaryPosition_raw]
    rfl
  have far : K.projectedGermFinish g - K.projectedGermStart g =
      Cap.horizontal (F.germDirection q.val) := by
    rw [SpatialFolding.germDirection, map_sub]
    rfl
  have point : F.boundaryPosition q = F.boundaryPosition e := by
    cases side
    · rfl
    · exact F.boundaryPosition_mate e
  have first := start.trans ((congrArg Cap.horizontal point).trans (L.position i))
  refine ⟨g, ?_, first, ?_⟩
  · cases side <;> rfl
  · have scalar : Cap.horizontal (F.germDirection q.val) =
        (if side then L.incoming i else L.outgoing i) • east := by
      cases side
      · exact L.outgoing_ray i
      · exact L.incoming_ray i
    rw [first, scalar] at far
    rw [show K.projectedGermFinish g =
        origin + L.time i • east + (if side then L.incoming i else L.outgoing i) • east by
      exact sub_eq_iff_eq_add'.mp far]
    rw [add_smul, ← add_assoc]

open Classical in
/-- The two named edges are ordered forward and backward on the physical link. -/
theorem exists_forward_contactGerms (i : I) :
    ∃ (left right : C.Germ) (a b : ℝ), a < L.time i ∧ L.time i < b ∧
      left.1.1 = L.earlierFace i ∧ right.1.1 = L.laterFace i ∧
      K.projectedGermStart left = origin + L.time i • east ∧
      K.projectedGermFinish left = origin + a • east ∧
      K.projectedGermStart right = origin + L.time i • east ∧
      K.projectedGermFinish right = origin + b • east := by
  obtain ⟨left, lf, ls, ll⟩ := L.exists_contactGerm i true
  obtain ⟨right, rf, rs, rl⟩ := L.exists_contactGerm i false
  simp only [ite_true, Bool.false_eq_true, ite_false] at ll rl
  rcases mul_neg_iff.mp (L.opposite i) with ⟨out, incoming⟩ | ⟨out, incoming⟩
  · rw [earlierFace, laterFace, decide_eq_true out, Bool.not_true]
    exact ⟨left, right, _, _, by linarith only [incoming], by linarith only [out],
      lf, rf, ls, ll, rs, rl⟩
  · rw [earlierFace, laterFace, decide_eq_false_iff_not.mpr (not_lt_of_ge out.le), Bool.not_false]
    exact ⟨right, left, _, _, by linarith only [out], by linarith only [incoming],
      rf, lf, rs, rl, ls, ll⟩

/-- The physical point on the closing line parameterized by time. -/
def horizontalContactPoint (origin : Plane) (t : ℝ) : Plane := origin + t • east

theorem horizontalContactPoint_injective (origin : Plane) :
    Function.Injective (horizontalContactPoint origin) := by
  intro u v equal
  have h := congrArg (fun p : Plane => p 0) equal
  change origin 0 + u * 1 = origin 0 + v * 1 at h
  linarith only [h]

/-- The consecutive piece's actual normal supports the roof at both of its end points. -/
theorem normalSlope_supports_of_contactGerm (g : C.Germ) {a b t : ℝ}
    (first : K.projectedGermStart g = horizontalContactPoint origin a)
    (last : K.projectedGermFinish g = horizontalContactPoint origin b)
    (within : t ∈ Set.uIcc a b) :
    K.normalSlope g.1.1 ∈ supportingSlopes K.roofHeight (horizontalContactPoint origin t) := by
  have hs : horizontalContactPoint origin t ∈ segment ℝ
      (horizontalContactPoint origin a) (horizontalContactPoint origin b) := by
    let f : ℝ →ᵃ[ℝ] Plane :=
      AffineMap.const ℝ ℝ origin + (LinearMap.toSpanSingleton ℝ Plane east).toAffineMap
    have form (x : ℝ) : f x = horizontalContactPoint origin x := rfl
    rw [← form, ← form, ← form, ← image_segment ℝ f, segment_eq_uIcc]
    exact Set.mem_image_of_mem f within
  rw [← first, ← last, K.projectedGerm_segment_eq] at hs
  apply K.normalSlope_supports
  symm
  exact K.roofHeight_eq_supportHeight_of_mem_projectedTriangle g.1.1
    ((K.projectedTriangle g.1.1).edge_subset _ hs)


open Classical in
theorem vertexAt_contact (i : I) :
    K.projectedVertex (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i))) =
        horizontalContactPoint origin (L.time i) := by
  let e := L.bank i
  change K.projectedVertex (C.vertexOfCorner Set.univ (e.val.1.1.val, e.val.1.2)) = _
  rw [K.projectedVertex_ofCorner]
  have h := L.position i
  rw [(K.folding.restrictFaces U).boundaryPosition_raw] at h
  exact h

private theorem supportingSlope_firstCoord_le {t s : ℝ} (lt : t < s)
    {p q : Plane} (first : p ∈ supportingSlopes K.roofHeight (horizontalContactPoint origin t))
    (last : q ∈ supportingSlopes K.roofHeight (horizontalContactPoint origin s)) :
    p 0 ≤ q 0 := by
  have h := supportingSlopes_monotone K.roofHeight _ _ _ _ first last
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at h
  change 0 ≤ (p 0 - q 0) * ((origin 0 + t * 1) - (origin 0 + s * 1)) +
    (p 1 - q 1) * ((origin 1 + t * 0) - (origin 1 + s * 0)) at h
  have sign : 0 ≤ (p 0 - q 0) * (t - s) := by nlinarith only [h]
  exact sub_nonpos.mp (nonpos_of_mul_nonneg_left sign (sub_neg.mpr lt))

/-- Monotonicity across each transverse contact, without selecting arbitrary
support planes on either side of the crease. -/
theorem firstCoord_earlierFace_le_laterFace (i : I) :
    K.normalSlope (L.earlierFace i) 0 ≤ K.normalSlope (L.laterFace i) 0 := by
  obtain ⟨left, right, a, b, ha, hb, lf, rf, ls, ll, rs, rl⟩ := L.exists_forward_contactGerms i
  have hp := normalSlope_supports_of_contactGerm left ls ll (Set.right_mem_uIcc (a := L.time i) (b := a))
  have hq := normalSlope_supports_of_contactGerm right rs rl (Set.right_mem_uIcc (a := L.time i) (b := b))
  rw [lf] at hp
  rw [rf] at hq
  exact supportingSlope_firstCoord_le (ha.trans hb) hp hq


theorem horizontalContactPoint_mem_openSegment {a b t : ℝ} (openWindow : t ∈ Set.uIoo a b) :
    horizontalContactPoint origin t ∈ openSegment ℝ
      (horizontalContactPoint origin a) (horizontalContactPoint origin b) := by
  let f : ℝ →ᵃ[ℝ] Plane :=
    AffineMap.const ℝ ℝ origin + (LinearMap.toSpanSingleton ℝ Plane east).toAffineMap
  have form (x : ℝ) : f x = horizontalContactPoint origin x := rfl
  rw [← form, ← form, ← form, ← image_openSegment ℝ f]
  apply Set.mem_image_of_mem
  have different : a ≠ b := by rintro rfl; simpa using openWindow
  rw [openSegment_eq_Ioo' different]
  exact openWindow

theorem projectedGerm_finish_time_of_next {g : C.Germ}
    {a b c : ℝ} (ab : a < b) (ac : a < c)
    (start : K.projectedGermStart g = horizontalContactPoint origin a)
    (finish : K.projectedGermFinish g = horizontalContactPoint origin c)
    (target : ∃ v : C.Vertex Set.univ, K.projectedVertex v = horizontalContactPoint origin b)
    (no_vertex : ∀ (t : ℝ), a < t → t < b →
      ¬ ∃ v : C.Vertex Set.univ, K.projectedVertex v = horizontalContactPoint origin t) :
    c = b := by
  refine le_antisymm ?_ ?_
  · by_contra! wrong
    obtain ⟨v, exact⟩ := target
    apply K.projectedVertex_not_mem_openGermSegment g v
    rw [exact, start, finish]
    exact horizontalContactPoint_mem_openSegment (Set.uIoo_of_le ac.le ▸ ⟨ab, wrong⟩)
  · by_contra! wrong
    apply no_vertex c ac wrong
    refine ⟨C.vertexOfCorner Set.univ (g.1.1, (C.germFarCorner g).2), ?_⟩
    rw [← finish]
    exact K.projectedVertex_ofCorner g.1.1 (C.germFarCorner g).2

/-- In the backward direction the first preceding vertex is again the germ's far end. -/
theorem projectedGerm_finish_time_of_previous {g : C.Germ} {a b c : ℝ}
    (ba : b < a) (ca : c < a)
    (start : K.projectedGermStart g = horizontalContactPoint origin a)
    (finish : K.projectedGermFinish g = horizontalContactPoint origin c)
    (target : ∃ v : C.Vertex Set.univ, K.projectedVertex v = horizontalContactPoint origin b)
    (no_vertex : ∀ (t : ℝ), b < t → t < a →
      ¬ ∃ v : C.Vertex Set.univ, K.projectedVertex v = horizontalContactPoint origin t) :
    c = b := by
  refine le_antisymm ?_ ?_
  · by_contra! bad
    apply no_vertex c bad ca
    refine ⟨C.vertexOfCorner Set.univ (g.1.1, (C.germFarCorner g).2), ?_⟩
    exact (K.projectedVertex_ofCorner g.1.1 (C.germFarCorner g).2).trans finish
  · by_contra! bad
    obtain ⟨v, exact⟩ := target
    apply K.projectedVertex_not_mem_openGermSegment g v
    rw [exact, start, finish]
    exact horizontalContactPoint_mem_openSegment (Set.uIoo_of_ge ca.le ▸ ⟨bad, ba⟩)

open Classical in
/-- The active planes on either name of a piece between consecutive closing
contacts agree as actual normals. The interval contains no refined vertex. -/
theorem laterFace_slope_eq_earlierFace_slope_of_next (i j : I) (ordered : L.time i < L.time j)
    (no_vertex : ∀ (t : ℝ), L.time i < t → t < L.time j →
      ¬ ∃ v : C.Vertex Set.univ, K.projectedVertex v = horizontalContactPoint origin t) :
    K.normalSlope (L.laterFace i) = K.normalSlope (L.earlierFace j) := by
  obtain ⟨_, forward, _, t, _, t_after, _, forward_face, _, _, forward_start, forward_finish⟩ :=
    L.exists_forward_contactGerms i
  obtain ⟨back, _, s, _, s_before, _, back_face, _, back_start, back_finish, _, _⟩ :=
    L.exists_forward_contactGerms j
  let target := C.includeRestrictedVertexUniv U
    ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank j))
  have position : K.projectedVertex target = horizontalContactPoint origin (L.time j) := L.vertexAt_contact j
  have ht := projectedGerm_finish_time_of_next ordered t_after forward_start forward_finish
    ⟨target, position⟩ no_vertex
  have hs : s = L.time i := projectedGerm_finish_time_of_previous ordered s_before back_start
    back_finish ⟨_, L.vertexAt_contact i⟩ no_vertex
  rw [ht] at forward_finish
  rw [hs] at back_finish
  have f₀ := normalSlope_supports_of_contactGerm forward forward_start forward_finish Set.left_mem_uIcc
  have f₁ := normalSlope_supports_of_contactGerm forward forward_start forward_finish Set.right_mem_uIcc
  have b₀ := normalSlope_supports_of_contactGerm back back_start back_finish Set.right_mem_uIcc
  have b₁ := normalSlope_supports_of_contactGerm back back_start back_finish Set.left_mem_uIcc
  have pq : K.normalSlope forward.1.1 0 = K.normalSlope back.1.1 0 :=
    (supportingSlope_firstCoord_le ordered f₀ b₁).antisymm (supportingSlope_firstCoord_le ordered b₀ f₁)
  obtain ⟨p, q, slopes, regular⟩ := L.regular j
  have f_at : C.vertexOfCorner Set.univ (forward.1.1, (C.germFarCorner forward).2) = target := by
    apply K.projectedVertex_injective
    exact (K.projectedVertex_ofCorner forward.1.1 (C.germFarCorner forward).2).trans
      (forward_finish.trans position.symm)
  have b_at : C.vertexOfCorner Set.univ (back.1.1, back.1.2) = target := by
    apply K.projectedVertex_injective
    exact (K.projectedVertex_ofCorner back.1.1 back.1.2).trans
      (back_start.trans position.symm)
  have same : K.normalSlope forward.1.1 = K.normalSlope back.1.1 := by
    have resolve (h : p 0 = q 0) : p = q := by
      rcases regular with eq | transv
      · exact eq
      · exfalso
        apply transv
        rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]
        change (p 0 - q 0) * 1 + (p 1 - q 1) * 0 = 0
        rw [h, sub_self, zero_mul, mul_zero, add_zero]
    rcases slopes _ _ f_at with h₁ | h₁ <;> rcases slopes _ _ b_at with h₂ | h₂
    · exact h₁.trans h₂.symm
    · rw [h₁, h₂] at pq ⊢
      exact resolve pq
    · rw [h₁, h₂] at pq ⊢
      exact (resolve pq.symm).symm
    · exact h₁.trans h₂.symm
  rwa [forward_face, back_face] at same

end Unfoldings.ConvexRoof.RegularClosingLink
