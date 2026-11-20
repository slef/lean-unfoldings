module

public import Unfoldings.Metric.BankStackSeamExcision
public import Unfoldings.Metric.Unglued

/-! A point on none of the actual bank marks retains a whole ball from its original piece. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} [Finite Edge] {Parameter : Edge → Type*}
  [∀ e, TopologicalSpace (Parameter e)]
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "L" => bankStackLeft X stack base gap
local notation "R" => bankStackRight X stack base gap
local notation "Banks" => bankSeams L R

/-- When the given point is on no marked bank, every sector in a sufficiently small
whole ball comes from the one original piece, with the original distances. -/
theorem bankStack_hasMetricBallChart_of_unmarked
    {Y : Type*} [MetricSpace Y] (a : Total X) (regular : HasMetricBallChart Y a.2)
    (unmarked : ∀ (slot : BankStackSlot stack) (t : Parameter slot.1),
      L slot t ≠ a ∧ R slot t ≠ a)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R₀ : ℝ} (Rpos : 0 < R₀)
    (cover : ∀ r, 0 < r → r ≤ R₀ → ∀ b : Total X,
      edist (point X Banks a) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks a ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r) :
    HasMetricBallChart Y (point X Banks a) := by
  have incident_free (b c : Total X) (h : Banks b c) : b ≠ a ∧ c ≠ a := by
    obtain ⟨slot, t, rfl, rfl⟩ := h
    exact unmarked slot t
  have stays {b c : Total X} (h : Relation.EqvGen Banks b c) : b = a ↔ c = a := by
    induction h with
    | rel b c h =>
      obtain ⟨hb, hc⟩ := incident_free b c h
      exact ⟨fun h => (hb h).elim, fun h => (hc h).elim⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have finite (i : Option G) : {c : X i | Relation.EqvGen Banks a ⟨i, c⟩}.Finite :=
    Set.Subsingleton.finite (by
      intro x hx y hy
      exact eq_of_heq (Sigma.mk.inj (((stays hx).mp rfl).trans ((stays hy).mp rfl).symm)).2)
  obtain ⟨δ, δpos, _, clearance⟩ := exists_bankStack_incident_slot_radius_le
    X stack base gap a finite base_closed gap_closed Rpos cover
  obtain ⟨r, rpos, comp, comp_center⟩ :=
    bankStack_exists_selected_forgetChart X stack base gap ∅ a δpos (by
      intro slot t near
      obtain ⟨u, hu, _⟩ := clearance δ δpos le_rfl slot t near
      exact ((unmarked slot u).1 ((stays hu).mp rfl)).elim)
  let noneKept : Total X → Total X → Prop := bankStackSelectedSeams X stack base gap ∅
  let emptySeams : Total X → Total X → Prop := fun _ _ => False
  let e : Realization X emptySeams ≃ᵢ Realization X noneKept :=
    changeSeamsIsometryEquiv X (fun _ _ h => h.elim) (fun _ _ h => by
      obtain ⟨s, _, _, _⟩ := h
      exact s.property.elim)
  have original : HasMetricBallChart Y (point X emptySeams a) := by
    obtain ⟨radius, pos, center, ⟨B⟩⟩ := regular
    let f : Metric.eball a.2 (ENNReal.ofReal radius) →
        Metric.eball (point X emptySeams a) (ENNReal.ofReal radius) :=
      fun x => ⟨of X emptySeams a.1 x.val,
        ((of_empty_isometry X a.1).edist_eq x.val a.2).trans_lt x.property⟩
    have iso : Isometry f := fun x y => (of_empty_isometry X a.1).edist_eq x.val y.val
    have onto : Function.Surjective f := by
      intro x
      obtain ⟨⟨j, y⟩, equal⟩ := point_surjective X emptySeams x.val
      have near : edist (of X emptySeams j y) (of X emptySeams a.1 a.2) <
          ENNReal.ofReal radius := by
        change edist (point X emptySeams ⟨j, y⟩) (point X emptySeams a) < ENNReal.ofReal radius
        rw [equal]
        exact x.property
      have tag : j = a.1 := by
        by_contra neq
        rw [edist_of_empty_of_ne X neq] at near
        exact (not_lt_of_ge le_top near).elim
      subst j
      rw [edist_of_empty] at near
      exact ⟨⟨y, near⟩, Subtype.ext equal⟩
    let F : Metric.eball a.2 (ENNReal.ofReal radius) ≃ᵢ
      Metric.eball (point X emptySeams a) (ENNReal.ofReal radius) :=
      ⟨Equiv.ofBijective f ⟨iso.injective, onto⟩, iso⟩
    exact ⟨radius, pos, center, ⟨F.symm.trans B⟩⟩
  have unglued : HasMetricBallChart Y (point X noneKept a) := original.isometryEquiv e
  exact unglued.of_centered_ball_equiv rpos comp comp_center

end Unfoldings.MetricGluing
