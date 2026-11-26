module

public import Unfoldings.Roof.HorizontalClosingEdges
public import Unfoldings.Roof.SupportedNormalTrace
public import Unfoldings.Topology.FiniteIntervalCover

/-! Ordered actual closing contacts concatenate into the normal trace used by Stokes' formula. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.RegularClosingLink

open Cap InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {U : Set Face} {origin : Plane} {I : Type*} [Fintype I]

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

variable (L : K.RegularClosingLink U origin east I)

open Classical in
private theorem contact_flat_of_same_firstCoord (i : I)
    (equal : K.normalSlope (L.earlierFace i) 0 = K.normalSlope (L.laterFace i) 0) :
    K.normalSlope (L.earlierFace i) = K.normalSlope (L.laterFace i) := by
  obtain ⟨left, right, a, b, _, _, lf, rf, ls, _, rs, _⟩ := L.exists_forward_contactGerms i
  let w := C.includeRestrictedVertexUniv U
    ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i))
  have w_at : K.projectedVertex w = horizontalContactPoint origin (L.time i) := L.vertexAt_contact i
  have corner (g : C.Germ) (position : K.projectedGermStart g = horizontalContactPoint origin (L.time i)) :
      C.vertexOfCorner Set.univ g.1 = w := by
    apply K.projectedVertex_injective
    rw [K.projectedVertex_ofCorner, w_at, ← position]
    rfl
  obtain ⟨p, q, slopes, regular⟩ := L.regular i
  have hlo := slopes _ _ (corner left ls)
  have hhi := slopes _ _ (corner right rs)
  rw [lf] at hlo
  rw [rf] at hhi
  have same (coords : p 0 = q 0) : p = q := by
    rcases regular with eq | transv
    · exact eq
    · exfalso
      apply transv
      rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]
      change (p 0 - q 0) * 1 + (p 1 - q 1) * 0 = 0
      rw [coords, sub_self, zero_mul, mul_zero, add_zero]
  rcases hlo with h | h <;> rcases hhi with k | k
  · exact h.trans k.symm
  · rw [h, k] at equal ⊢
    exact same equal
  · rw [h, k] at equal ⊢
    exact (same equal.symm).symm
  · exact h.trans k.symm

open Classical in
/-- The positions of the actual finite contacts admit their unique forward ordering. -/
theorem exists_ordered_contact_indices :
    ∃ index : Fin (Fintype.card I) ≃ I, StrictMono (fun i => L.time (index i)) := by
  let s := Finset.univ.image L.time
  have card : s.card = Fintype.card I :=
    (Finset.card_image_of_injective _ L.distinct).trans Finset.card_univ
  let E : I ≃ s := Equiv.ofBijective
    (fun i => ⟨L.time i, Finset.mem_image_of_mem L.time (Finset.mem_univ i)⟩) ⟨by
      intro i j same
      exact L.distinct (congrArg Subtype.val same), by
      rintro ⟨t, member⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
      exact ⟨i, rfl⟩⟩
  let e := (s.orderIsoOfFin card).toEquiv.trans E.symm
  refine ⟨e, ?_⟩
  have coordinate (i : Fin (Fintype.card I)) : L.time (e i) = s.orderEmbOfFin card i :=
    congrArg Subtype.val (E.apply_symm_apply (s.orderIsoOfFin card i))
  intro i j before
  change L.time (e i) < L.time (e j)
  rw [coordinate i, coordinate j]
  exact (s.orderEmbOfFin card).strictMono before

open Classical in
/-- Construct the actual normal trace of the regular closing contacts, retaining
the exact signed sum and both active endpoint slopes. -/
theorem exists_supportedNormalTrace_of_order {n : ℕ} (e : Fin (n + 1) ≃ I)
    (ordered : StrictMono fun i => L.time (e i))
    (no_vertex : ∀ i : Fin n, ∀ t : ℝ, L.time (e i.castSucc) < t → t < L.time (e i.succ) →
      ¬ ∃ w : C.Vertex Set.univ, K.projectedVertex w = horizontalContactPoint origin t)
    (above : ∀ i (g : C.LinkGerm Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i)))),
      g.val.1.1 ∈ U → 0 ≤ K.projectedGermRay g 1)
    {cell : Set Plane} (slopes : ∀ f, K.normalSlope f ∈ cell) :
    ∃ T : K.SupportedNormalTrace cell (origin 1) (n + 1),
      T.path.vertex 0 = K.normalSlope (L.earlierFace (e 0)) ∧
      T.path.vertex (Fin.last (n + 1)) = K.normalSlope (L.laterFace (e (Fin.last n))) ∧
      T.hingeSum = ∑ i : I, K.restrictedBoundaryTurnError U (L.bank i) := by
  let first (i : Fin (n + 1)) := K.normalSlope (L.earlierFace (e i))
  let last (i : Fin (n + 1)) := K.normalSlope (L.laterFace (e i))
  let face (i : Fin (n + 2)) := if hi : i.val < n + 1 then L.earlierFace (e ⟨i.val, hi⟩)
    else L.laterFace (e (Fin.last n))
  let P : PolygonalChain Plane (n + 1) := ⟨fun i => K.normalSlope (face i)⟩
  have at_left (i : Fin (n + 1)) : P.vertex i.castSucc = first i := by
    simp only [P, face, Fin.val_castSucc, dite_eq_left i.isLt, first]
  have at_right (i : Fin (n + 1)) : P.vertex i.succ = last i := by
    by_cases hi : i.val < n
    · let j : Fin n := ⟨i.val, hi⟩
      have at_i : j.castSucc = i := Fin.ext rfl
      have at_next : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = j.succ := Fin.ext rfl
      have ord : L.time (e j.castSucc) < L.time (e j.succ) := ordered Fin.castSucc_lt_succ
      have normal := L.laterFace_slope_eq_earlierFace_slope_of_next _ _ ord (no_vertex j)
      rw [at_i] at normal
      change K.normalSlope (face i.succ) = last i
      unfold face
      rw [dite_eq_left (show i.succ.val < n + 1 by exact Nat.succ_lt_succ hi)]
      change K.normalSlope (L.earlierFace (e ⟨i.val + 1, _⟩)) = last i
      rw [at_next]
      exact normal.symm
    · have index : i = Fin.last n := Fin.ext (by change i.val = n; have := i.isLt; omega)
      change K.normalSlope (face i.succ) = last i
      unfold face
      rw [dite_eq_right (show ¬i.succ.val < n + 1 by simpa only [Fin.val_succ, Nat.succ_lt_succ_iff] using hi)]
      rw [index]
  choose m b begin_line end_line turns using fun i : Fin (n + 1) =>
    L.exists_signed_horizontal_turn (e i) (above (e i))
  let T : K.SupportedNormalTrace cell (origin 1) (n + 1) := {
    path := P
    advancing := fun i => by
      change 0 ≤ P.vertex i.succ 0 - P.vertex i.castSucc 0
      rw [at_left i, at_right i, sub_nonneg]
      exact L.firstCoord_earlierFace_le_laterFace (e i)
    flat := fun i h => by
      change P.vertex i.succ 0 - P.vertex i.castSucc 0 = 0 at h
      rw [at_left i, at_right i, sub_eq_zero] at h
      change P.vertex i.succ - P.vertex i.castSucc = 0
      rw [at_left i, at_right i]
      change K.normalSlope (L.laterFace (e i)) - K.normalSlope (L.earlierFace (e i)) = 0
      rw [L.contact_flat_of_same_firstCoord (e i) h.symm, sub_self]
    inside := fun i => slopes (face i)
    contact := fun i => horizontalContactPoint origin (L.time (e i))
    on_line := fun i => by
      change origin 1 + L.time (e i) * 0 = origin 1
      ring
    left_support := fun i => by
      rw [at_left i]
      apply K.normalSlope_supports
      exact L.contactFace_active (e i) _
    right_support := fun i => by
      rw [at_right i]
      apply K.normalSlope_supports
      exact L.contactFace_active (e i) _
    slope := m
    intercept := b
    left_normal_line := fun i => by rw [at_left i]; exact begin_line i
    right_normal_line := fun i => by rw [at_right i]; exact end_line i
  }
  refine ⟨T, at_left 0, at_right (Fin.last n), ?_⟩
  unfold SupportedNormalTrace.hingeSum
  change (∑ i : Fin (n + 1), hingeAngleChange (m i) (b i) (P.vertex i.castSucc 0) (P.vertex i.succ 0)) = _
  simp_rw [at_left, at_right]
  change (∑ i : Fin (n + 1), hingeAngleChange (m i) (b i)
    (K.normalSlope (L.earlierFace (e i)) 0) (K.normalSlope (L.laterFace (e i)) 0)) = _
  simp_rw [← turns]
  exact Equiv.sum_comp e (fun i : I => K.restrictedBoundaryTurnError U (L.bank i))

end Unfoldings.ConvexRoof.RegularClosingLink
