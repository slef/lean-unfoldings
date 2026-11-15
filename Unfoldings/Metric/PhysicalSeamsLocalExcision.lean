module

public import Unfoldings.Metric.PhysicalSeamsSplit
public import Unfoldings.Metric.Excision

/-! Local agreement of physical seam pieces preserves a whole intrinsic ball, even on a cut. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.PhysicalSeams

variable {I X : Type*} [Finite I] [MetricSpace X] {cells : I → Set X}
  (S T : PhysicalSeams cells)

/-- Restoring distant attachment pieces leaves a whole metric ball unchanged, including
centers lying on cuts. Only local carrier agreement is required, not entire incident seams. -/
theorem exists_forgetChart_of_local_carriers
    (included : ∀ i j, S.carrier i j ⊆ T.carrier i j) (a : Total (fun i => cells i))
    {ε : ℝ} (positive : 0 < ε)
    (local_agreement : ∀ i j x, dist x a.2.val < ε → x ∈ T.carrier i j → x ∈ S.carrier i j) :
    Nonempty (ForgetChart (fun i => cells i) (S.relation_mono included) a) := by
  let pieces : Bool → Set X := fun near =>
    if near then Metric.closedBall a.2.val (ε / 2) else (Metric.ball a.2.val (ε / 4))ᶜ
  have pieces_closed : ∀ side, IsClosed (pieces side) := by
    intro side
    cases side
    · exact Metric.isOpen_ball.isClosed_compl
    · exact Metric.isClosed_closedBall
  have cover : (⋃ side, pieces side) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases close : dist x a.2.val ≤ ε / 2
    · exact Set.mem_iUnion.mpr ⟨true, close⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨false, ?_⟩
      change ¬ dist x a.2.val < ε / 4
      linarith
  let Q := T.splitClosedSeams pieces pieces_closed
  have relation : Q.relation = T.relation := by
    funext x y
    exact propext (T.splitClosedSeams_relation_iff pieces pieces_closed cover x y)
  have finite : ∀ i, (classIn (fun i => cells i) Q.relation a i).Finite := by
    intro i
    rw [relation]
    exact (T.classIn_subsingleton a i).finite
  have compatible : ∀ s, Q.Incident a s → ∀ x,
      of (fun i => cells i) S.relation (Q.left s) (Q.toLeft s x) =
        of (fun i => cells i) S.relation (Q.right s) (Q.toRight s x) := by
    rintro ⟨⟨i, j⟩, side⟩ incident x
    cases side
    · obtain ⟨p, hp, w, rfl⟩ := incident
      rw [relation] at hp
      have same : a.2.val = w.val := T.physical_eq_of_eqvGen hp
      have absent : w.val ∉ Metric.ball a.2.val (ε / 4) := w.property.2
      apply False.elim
      apply absent
      rw [← same, Metric.mem_ball, dist_self]
      exact div_pos positive (by norm_num)
    · apply point_eq_of_glue
      refine ⟨(i, j), ⟨x.val, ?_⟩, rfl, rfl⟩
      apply local_agreement i j x.val ?_ x.property.1
      have close : dist x.val a.2.val ≤ ε / 2 := x.property.2
      linarith
  have comparison := Q.exists_radius_map_edist_le a finite (of (fun i => cells i) S.relation)
    (of_lipschitz (fun i => cells i) S.relation) compatible
  rw [relation] at comparison
  obtain ⟨r, rpos, lower⟩ := comparison
  exact ⟨⟨r, rpos, forgetBallIsometry (fun i => cells i) (S.relation_mono included)
    a (ENNReal.ofReal_pos.mpr rpos) lower, fun _ => rfl⟩⟩

end Unfoldings.MetricGluing.PhysicalSeams
