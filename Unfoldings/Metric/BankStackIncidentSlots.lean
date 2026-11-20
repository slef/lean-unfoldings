module

public import Unfoldings.Metric.BankStackCurves
public import Unfoldings.Metric.Barrier

/-! Near a finite intrinsic graft class, a slot can occur only if it contains a center mark. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricBarrier

/-- Finite center copies and a closed subset admit a common clearance in an extended
metric space. Points sufficiently close to the closed subset lie in it. -/
theorem exists_emetric_radius_near_closed {X : Type*} [EMetricSpace X] {s t : Set X}
    (finite : s.Finite) (closed : IsClosed t) :
    ∃ r > 0, ∀ x ∈ t, ∀ c ∈ s, edist c x < ENNReal.ofReal r → c ∈ t := by
  classical
  let _ : Finite s := finite.to_subtype
  have pointwise (c : s) : ∃ r > 0, ∀ x ∈ t, edist c.val x < ENNReal.ofReal r → c.val ∈ t := by
    by_cases member : c.val ∈ t
    · exact ⟨1, zero_lt_one, fun _ _ _ => member⟩
    · obtain ⟨δ, δpos, outside⟩ := EMetric.isOpen_iff.mp closed.isOpen_compl c.val member
      have finite_δ : min δ 1 ≠ ∞ := ((min_le_right δ 1).trans_lt ENNReal.one_lt_top).ne
      have positive := ENNReal.toReal_pos (lt_min δpos zero_lt_one).ne' finite_δ
      refine ⟨(min δ 1).toReal, positive, fun x hx near => ?_⟩
      rw [ENNReal.ofReal_toReal finite_δ] at near
      have h : x ∈ Metric.eball c.val δ :=
        (edist_comm x c.val).trans_lt (near.trans_le (min_le_left δ 1))
      exact (outside h hx).elim
  choose radius positive bound using pointwise
  obtain ⟨r, rpos, small⟩ := exists_pos_le_of_finite radius positive
  exact ⟨r, rpos, fun x hx c hc near =>
    bound ⟨c, hc⟩ x hx (near.trans_le (ENNReal.ofReal_le_ofReal (small ⟨c, hc⟩)))⟩

end Unfoldings.MetricBarrier

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} [Finite Edge] {Parameter : Edge → Type*}
  [∀ e, TopologicalSpace (Parameter e)]
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "Left" => bankStackLeft X stack base gap
local notation "Right" => bankStackRight X stack base gap
local notation "Banks" => bankSeams Left Right
local notation "Index" => bankStackLeftPiece stack X base gap
local notation "Curve" => bankStackLeftCurve stack X base gap

/-- In a small whole graft ball, a seam point is near a center representative on
that same original slot. No change of its arclength or bank addresses is needed. -/
theorem exists_bankStack_incident_slot_radius_le (a : Total X)
    (finite : ∀ i, {c : X i | Relation.EqvGen Banks a ⟨i, c⟩}.Finite)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (Rpos : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (point X Banks a) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks a ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r) :
    ∃ r > 0, r ≤ R ∧ ∀ ρ, 0 < ρ → ρ ≤ r →
      ∀ slot : BankStackSlot stack, ∀ t : Parameter slot.1,
        edist (point X Banks a) (point X Banks (Left slot t)) < ENNReal.ofReal ρ →
        ∃ u : Parameter slot.1, Relation.EqvGen Banks a (Left slot u) ∧
          edist (Curve slot u) (Curve slot t) < ENNReal.ofReal ρ := by
  have slot_clearance (slot : BankStackSlot stack) :=
    MetricBarrier.exists_emetric_radius_near_closed (finite (Index slot))
      (bankStackLeftCurve_closed stack X base gap base_closed gap_closed slot).isClosed_range
  choose δ δpos clear using slot_clearance
  obtain ⟨ε, εpos, bounds⟩ := MetricBarrier.exists_pos_le_of_finite δ δpos
  let r := min R ε
  have rpos : 0 < r := lt_min Rpos εpos
  refine ⟨r, rpos, min_le_left _ _, ?_⟩
  intro ρ ρpos small slot t near
  have eq := bankStackLeft_curve stack X base gap slot t
  have near' : edist (point X Banks a) (point X Banks ⟨Index slot, Curve slot t⟩) <
      ENNReal.ofReal ρ := eq ▸ near
  obtain ⟨c, hc, close⟩ := cover ρ ρpos (small.trans (min_le_left _ _)) _ near'
  have member : c ∈ Set.range (Curve slot) :=
    clear slot (Curve slot t) (Set.mem_range_self t) c hc
      (close.trans_le (ENNReal.ofReal_le_ofReal
        (small.trans ((min_le_right _ _).trans (bounds slot)))))
  obtain ⟨u, rfl⟩ := member
  exact ⟨u, (bankStackLeft_curve stack X base gap slot u).symm ▸ hc, close⟩

/-- A whole seam slot near the chosen class contains an original center copy. -/
theorem exists_bankStack_incident_slot_radius (a : Total X)
    (finite : ∀ i, {c : X i | Relation.EqvGen Banks a ⟨i, c⟩}.Finite)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (Rpos : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (point X Banks a) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks a ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r) :
    ∃ r > 0, ∀ slot : BankStackSlot stack, ∀ t : Parameter slot.1,
      edist (point X Banks a) (point X Banks (Left slot t)) < ENNReal.ofReal r →
      ∃ u : Parameter slot.1, Relation.EqvGen Banks a (Left slot u) ∧
        edist (Curve slot u) (Curve slot t) < ENNReal.ofReal r := by
  obtain ⟨r, rpos, _, near⟩ := exists_bankStack_incident_slot_radius_le X stack base gap a
    finite base_closed gap_closed Rpos cover
  exact ⟨r, rpos, near r rpos le_rfl⟩

end Unfoldings.MetricGluing
