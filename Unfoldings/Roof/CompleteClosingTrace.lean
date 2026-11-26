module

public import Unfoldings.Roof.ClosingContactTrace

/-! Completing the trace on a horizontal segment also identifies its two endpoint faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.RegularClosingLink

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {U : Set Face} {origin stop : Plane} {length : ℝ}

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)
local notation "pt" => horizontalContactPoint origin
local notation "Contact" => {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ origin stop}

open Classical in
set_option maxHeartbeats 1700000 in
/-- A complete list of actual contacts gives the normal chain and the actual
closing edges at the two ends of the segment. -/
theorem exists_complete_supportedNormalTrace
    (L : K.RegularClosingLink U origin east Contact) (nonempty : Nonempty Contact)
    (stop_at : pt length = stop)
    (times : ∀ i, 0 < L.time i ∧ L.time i < length)
    (actual : ∀ i : Contact, K.projectedVertex i.val = pt (L.time i))
    (left right : C.Vertex Set.univ)
    (left_at : K.projectedVertex left = pt 0) (right_at : K.projectedVertex right = pt length)
    (above : ∀ i (g : C.LinkGerm Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i)))),
      g.val.1.1 ∈ U → 0 ≤ K.projectedGermRay g 1)
    {cell : Set Plane} (slopes : ∀ f, K.normalSlope f ∈ cell) :
    ∃ (n : ℕ) (T : K.SupportedNormalTrace cell (origin 1) (n + 1))
      (first last : C.Germ) (a b : ℝ),
      0 < a ∧ b < length ∧
      K.projectedGermStart first = pt a ∧ K.projectedGermFinish first = pt 0 ∧
      K.projectedGermStart last = pt b ∧ K.projectedGermFinish last = pt length ∧
      T.path.vertex 0 = K.normalSlope first.1.1 ∧
      T.path.vertex (Fin.last (n + 1)) = K.normalSlope last.1.1 ∧
      T.hingeSum = ∑ i : Contact, K.restrictedBoundaryTurnError U (L.bank i) := by
  let n := Fintype.card Contact - 1
  have count : n + 1 = Fintype.card Contact :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr nonempty))
  obtain ⟨index, monotone⟩ := L.exists_ordered_contact_indices
  let e : Fin (n + 1) ≃ Contact := (finCongr count).trans index
  have ordered : StrictMono (fun i => L.time (e i)) := by
    intro i j lt
    apply monotone
    exact Fin.lt_def.mpr lt
  have complete (t : ℝ) (pos : 0 < t) (before : t < length) (w : C.Vertex Set.univ)
      (at_w : K.projectedVertex w = pt t) : ∃ j : Fin (n + 1), L.time (e j) = t := by
    have on : K.projectedVertex w ∈ openSegment ℝ origin stop := by
      have inside : t ∈ Set.uIoo 0 length := by
        rw [Set.uIoo_of_le (pos.trans before).le]
        exact ⟨pos, before⟩
      have on_segment := horizontalContactPoint_mem_openSegment (origin := origin) inside
      have start : pt 0 = origin := by simp [horizontalContactPoint]
      rwa [← at_w, start, stop_at] at on_segment
    let contact : Contact := ⟨w, on⟩
    refine ⟨e.symm contact, horizontalContactPoint_injective origin ?_⟩
    rw [e.apply_symm_apply]
    exact (actual contact).symm.trans at_w
  have no_middle (i : Fin n) (t : ℝ) (lo : L.time (e i.castSucc) < t)
      (hi : t < L.time (e i.succ)) :
      ¬ ∃ w : C.Vertex Set.univ, K.projectedVertex w = pt t := by
    rintro ⟨w, at_w⟩
    obtain ⟨j, eq⟩ := complete t ((times _).1.trans lo) (hi.trans (times _).2) w at_w
    have earlier : i.castSucc < j := ordered.lt_iff_lt.mp (lo.trans_eq eq.symm)
    have later : j < i.succ := ordered.lt_iff_lt.mp (eq.trans_lt hi)
    change i.val < j.val at earlier
    change j.val < i.val + 1 at later
    omega
  have no_first (t : ℝ) (lo : 0 < t) (hi : t < L.time (e 0)) :
      ¬ ∃ w : C.Vertex Set.univ, K.projectedVertex w = pt t := by
    rintro ⟨w, at_w⟩
    obtain ⟨j, eq⟩ := complete t lo (hi.trans (times _).2) w at_w
    exact hi.not_ge (eq ▸ ordered.monotone (Fin.zero_le j))
  have no_last (t : ℝ) (lo : L.time (e (Fin.last n)) < t) (hi : t < length) :
      ¬ ∃ w : C.Vertex Set.univ, K.projectedVertex w = pt t := by
    rintro ⟨w, at_w⟩
    obtain ⟨j, eq⟩ := complete t ((times _).1.trans lo) hi w at_w
    exact lo.not_ge (eq ▸ ordered.monotone (Fin.le_last j))
  obtain ⟨T, first_eq, last_eq, turn⟩ :=
    L.exists_supportedNormalTrace_of_order e ordered no_middle above slopes
  obtain ⟨first, _, a, _, at_a, _, first_face, _, f_start, f_end, _, _⟩ :=
    L.exists_forward_contactGerms (e 0)
  obtain ⟨_, last, _, b, _, at_b, _, last_face, _, _, l_start, l_end⟩ :=
    L.exists_forward_contactGerms (e (Fin.last n))
  have a_eq := projectedGerm_finish_time_of_previous (times (e 0)).1 at_a
    f_start f_end ⟨left, left_at⟩ no_first
  have b_eq := projectedGerm_finish_time_of_next (times (e (Fin.last n))).2 at_b
    l_start l_end ⟨right, right_at⟩ no_last
  rw [← first_face] at first_eq
  rw [← last_face] at last_eq
  exact ⟨n, T, first, last, _, _, (times _).1, (times _).2, f_start,
    a_eq ▸ f_end, l_start, b_eq ▸ l_end, first_eq, last_eq, turn⟩

end Unfoldings.ConvexRoof.RegularClosingLink
