module

public import Unfoldings.Metric.LocalMap
public import Unfoldings.Metric.Unglued
public import Unfoldings.Metric.FiniteBankHalfPlaneGluing
public import Unfoldings.Metric.LocalBallRegularity
public import Unfoldings.Metric.ChangeSeams
public import Unfoldings.Metric.BankStackLocalClasses
public import Unfoldings.Metric.BankStackIncidentSlots

/-! Retaining the slots that occur in a neighborhood keeps its whole intrinsic metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

section

variable {I : Type*} (E : I → Type*) [∀ i, EMetricSpace (E i)]
  {Y : Type*} [EMetricSpace Y]

/-- A short metric distance suffices to bound a map from local route-step estimates. -/
private theorem map_edist_le_edist_of_route_budget (glue : Total E → Total E → Prop)
    (f : Total E → Y) (center : Realization E glue) (r : ℝ≥0∞)
    (local_step : ∀ a b, edist center (point E glue a) < r →
      edist center (point E glue b) < r → edist (f a) (f b) ≤ stepCost E glue a b)
    (a b : Total E)
    (budget : edist center (point E glue a) +
      edist (point E glue a) (point E glue b) < r) :
    edist (f a) (f b) ≤ edist (point E glue a) (point E glue b) := by
  by_contra smaller
  let d := edist (point E glue a) (point E glue b)
  let D := edist center (point E glue a)
  have less : d < min (edist (f a) (f b)) (r - D) :=
    lt_min (lt_of_not_ge smaller) (lt_tsub_iff_left.mpr budget)
  obtain ⟨route, short⟩ := iInf_lt_iff.mp less
  have fits : D + route.length (stepCost E glue) < r :=
    lt_tsub_iff_left.mp (short.trans_le (min_le_right _ _))
  have bound := map_edist_le_length_of_short_route E glue f center r local_step route fits
  exact (not_lt_of_ge bound) (short.trans_le (min_le_left _ _))


/-- If a neighborhood contains no seam endpoint, its original piece preserves distances there. -/
theorem of_isometry_on_ball_of_no_seams (glue : Total E → Total E → Prop)
    (i : I) (x : E i) {δ : ℝ} (positive : 0 < δ)
    (outside : ∀ a b, glue a b → edist (of E glue i x) (point E glue a) ≥ ENNReal.ofReal δ) :
    Isometry (fun p : Metric.eball x (ENNReal.ofReal (δ / 3)) => of E glue i p.val) := by
  classical
  let empty : Total E → Total E → Prop := fun _ _ => False
  let center := of E glue i x
  let r := δ / 3
  have rpos : 0 < r := div_pos positive (by norm_num)
  have step (a b : Total E) (ha : edist center (point E glue a) < ENNReal.ofReal δ)
      (hb : edist center (point E glue b) < ENNReal.ofReal δ) :
      edist (point E empty a) (point E empty b) ≤ stepCost E glue a b := by
    have unjoined : ¬ (glue a b ∨ glue b a) := fun h =>
      h.elim (fun h => (not_lt_of_ge (outside a b h)) ha)
        (fun h => (not_lt_of_ge (outside b a h)) hb)
    rw [stepCost, if_neg unjoined]
    exact (Route.distance_le_cost (stepCost E empty) a b).trans (stepCost_le_faceCost E empty a b)
  intro p q
  let ap : Total E := ⟨i, p.val⟩
  let aq : Total E := ⟨i, q.val⟩
  change edist (point E glue ap) (point E glue aq) = edist p.val q.val
  apply le_antisymm (edist_of_le E glue i p.val q.val)
  have near (w : Metric.eball x (ENNReal.ofReal r)) :
      edist center (of E glue i w.val) < ENNReal.ofReal r := by
    rw [edist_comm]
    exact (edist_of_le E glue i w.val x).trans_lt w.property
  have chord : edist (point E glue ap) (point E glue aq) <
      ENNReal.ofReal r + ENNReal.ofReal r :=
    (edist_triangle _ center _).trans_lt
      (ENNReal.add_lt_add ((edist_comm _ _).trans_lt (near p)) (near q))
  have sum : ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add rpos.le rpos.le, ← ENNReal.ofReal_add rpos.le (by positivity)]
    congr 1
    dsimp [r]
    ring
  have budget := (ENNReal.add_lt_add (near p) chord).trans_le sum.le
  have lower := map_edist_le_edist_of_route_budget E glue (point E empty)
    center (ENNReal.ofReal δ) step ap aq budget
  exact ((of_empty_isometry E i).edist_eq p.val q.val).symm.le.trans lower

end

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "L" => bankStackLeft X stack base gap
local notation "Rgt" => bankStackRight X stack base gap
local notation "Banks" => bankSeams L Rgt

/-- Keep precisely the selected consecutive original bank slots with their whole domains. -/
def bankStackSelectedSeams (keep : Set (BankStackSlot stack)) : Total X → Total X → Prop :=
  bankSeams (fun slot : keep => L slot.val) (fun slot : keep => Rgt slot.val)

omit [∀ i, EMetricSpace (X i)] in
variable {X stack base gap} in
theorem bankStackSelectedSeams_included (keep : Set (BankStackSlot stack)) (a b : Total X)
    (joined : bankStackSelectedSeams X stack base gap keep a b) : Banks a b := by
  obtain ⟨s, t, first, last⟩ := joined
  exact ⟨s.val, t, first, last⟩

private theorem exists_centered_ball_forget
    {I : Type*} (E : I → Type*) [∀ i, EMetricSpace (E i)] {P Q : Total E → Total E → Prop}
    (incl : ∀ x y, P x y → Q x y) (a : Total E) {r : ℝ} (positive : 0 < r)
    (lower : ∀ b c,
      edist (point E Q a) (point E Q b) < ENNReal.ofReal r →
      edist (point E Q a) (point E Q c) < ENNReal.ofReal r →
      edist (point E P b) (point E P c) ≤ edist (point E Q b) (point E Q c)) :
    ∃ A : Metric.eball (point E P a) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (point E Q a) (ENNReal.ofReal r),
      (A ⟨point E P a, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
        point E Q a := by
  have upper (b c : Total E) : edist (point E Q b) (point E Q c) ≤
      edist (point E P b) (point E P c) := distance_antitone E incl b c
  let f (z : Metric.eball (point E P a) (ENNReal.ofReal r)) :
      Metric.eball (point E Q a) (ENNReal.ofReal r) :=
    ⟨forget E incl z.val, by
      have bound := (forget_lipschitz E incl).edist_le_mul z.val (point E P a)
      simp only [ENNReal.coe_one, one_mul, forget_point] at bound
      exact bound.trans_lt z.property⟩
  have isometric : Isometry f := by
    intro x y
    obtain ⟨b, hb⟩ := point_surjective E P x.val
    obtain ⟨c, hc⟩ := point_surjective E P y.val
    have near (d : Total E) (hd : edist (point E P d) (point E P a) < ENNReal.ofReal r) :
        edist (point E Q a) (point E Q d) < ENNReal.ofReal r :=
      (upper a d).trans_lt ((edist_comm _ _).trans_lt hd)
    change edist (forget E incl x.val) (forget E incl y.val) = edist x.val y.val
    rw [← hb, ← hc, forget_point, forget_point]
    exact le_antisymm (upper b c)
      (lower b c (near b (hb.symm ▸ x.property)) (near c (hc.symm ▸ y.property)))
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨b, hb⟩ := point_surjective E Q y.val
    have near : edist (point E Q a) (point E Q b) < ENNReal.ofReal r :=
      (edist_comm _ _).trans_lt (hb.symm ▸ y.property)
    have root := Metric.mem_eball_self (x := point E Q a) (ENNReal.ofReal_pos.mpr positive)
    have fit := (lower a b root near).trans_lt near
    exact ⟨⟨point E P b, (edist_comm _ _).trans_lt fit⟩, Subtype.ext hb⟩
  exact ⟨⟨Equiv.ofBijective f ⟨isometric.injective, onto⟩, isometric⟩, rfl⟩

/-- If every sufficiently nearby bank point uses a retained slot, a whole ball can be
compared using exactly the same piecewise distances after discarding the other slots. -/
theorem bankStack_exists_selected_forgetChart (keep : Set (BankStackSlot stack)) (a : Total X)
    {δ : ℝ} (positive : 0 < δ)
    (retained : ∀ s t, edist (point X Banks a) (point X Banks (L s t)) < ENNReal.ofReal δ →
      s ∈ keep) :
    ∃ (r : ℝ) (pos : 0 < r),
      ∃ A : Metric.eball (point X (bankStackSelectedSeams X stack base gap keep) a)
          (ENNReal.ofReal r) ≃ᵢ Metric.eball (point X Banks a) (ENNReal.ofReal r),
        (A ⟨point X (bankStackSelectedSeams X stack base gap keep) a,
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr pos)⟩).val = point X Banks a := by
  classical
  let S := bankStackSelectedSeams X stack base gap keep
  let center := point X Banks a
  let f := point X S
  have compatible (b c : Total X) (near : edist center (point X Banks b) < ENNReal.ofReal δ)
      (joined : Banks b c) : f b = f c := by
    obtain ⟨s, t, rfl, rfl⟩ := joined
    exact point_eq_of_glue X (glue := S) ⟨⟨s, retained s t near⟩, t, rfl, rfl⟩
  have step (b c : Total X)
      (hb : edist center (point X Banks b) < ENNReal.ofReal δ)
      (hc : edist center (point X Banks c) < ENNReal.ofReal δ) :
      edist (f b) (f c) ≤ stepCost X Banks b c := by
    by_cases joined : Banks b c ∨ Banks c b
    · have equal := joined.elim (compatible b c hb) (fun h => (compatible c b hc h).symm)
      simp [stepCost, joined, equal]
    · obtain ⟨i, b⟩ := b
      obtain ⟨j, c⟩ := c
      by_cases same : i = j
      · subst j
        change edist (of X S i b) (of X S i c) ≤ _
        simpa [stepCost, joined, faceCost] using edist_of_le X S i b c
      · simp [stepCost, joined, faceCost, same]
  let r := δ / 3
  have rpos : 0 < r := div_pos positive (by norm_num)
  have lower (b c : Total X)
      (hb : edist center (point X Banks b) < ENNReal.ofReal r)
      (hc : edist center (point X Banks c) < ENNReal.ofReal r) :
      edist (f b) (f c) ≤ edist (point X Banks b) (point X Banks c) := by
    have chord := (edist_triangle (point X Banks b) center (point X Banks c)).trans_lt
      (ENNReal.add_lt_add ((edist_comm _ _).trans_lt hb) hc)
    have room := ENNReal.add_lt_add hb chord
    have sum : ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add rpos.le rpos.le,
        ← ENNReal.ofReal_add rpos.le (add_nonneg rpos.le rpos.le)]
      congr 1
      dsimp [r]
      ring
    exact map_edist_le_edist_of_route_budget X Banks f center _ step b c (room.trans_le sum.le)
  exact ⟨r, rpos, exists_centered_ball_forget X
    (bankStackSelectedSeams_included keep) a rpos lower⟩

variable [Finite Edge] [∀ e, TopologicalSpace (Parameter e)]

/-- At an ordinary seam there are only its two center marks. Restricting to its
single original slot gives a whole-ball isometry, even when both ends are in one piece. -/
theorem bankStack_exists_single_forgetChart (slot : BankStackSlot stack) (t : Parameter slot.1)
    (nodup : ∀ e, (stack e).Nodup)
    (unique : BankStackUniqueMarksAt stack X base gap slot.1 t)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (positive : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (point X Banks (L slot t)) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1,
        Relation.EqvGen Banks (L slot t) ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r) :
    ∃ (r : ℝ) (pos : 0 < r),
      ∃ A : Metric.eball (point X (bankStackSelectedSeams X stack base gap {slot}) (L slot t))
          (ENNReal.ofReal r) ≃ᵢ Metric.eball (point X Banks (L slot t)) (ENNReal.ofReal r),
        (A ⟨point X (bankStackSelectedSeams X stack base gap {slot}) (L slot t),
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr pos)⟩).val = point X Banks (L slot t) := by
  have finite (i : Option G) :
      {q : X i | Relation.EqvGen Banks (L slot t) ⟨i, q⟩}.Finite := by
    have candidates := (Set.finite_singleton (L slot t)).union (Set.finite_singleton (Rgt slot t))
    have injective : Function.Injective (fun q : X i => (⟨i, q⟩ : Total X)) :=
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
    exact (candidates.preimage injective.injOn).subset fun _ h =>
      (bankStack_eqvGen_pair_iff stack X base gap nodup slot t unique _).mp h
  obtain ⟨δ, δpos, near_slot⟩ := exists_bankStack_incident_slot_radius X stack base gap
    (L slot t) finite base_closed gap_closed positive cover
  apply bankStack_exists_selected_forgetChart X stack base gap {slot} (L slot t) δpos
  intro s u near
  obtain ⟨v, related, _⟩ := near_slot s u near
  rcases (bankStack_eqvGen_pair_iff stack X base gap nodup slot t unique _).mp related with
    first | last
  · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      false false s v first
    exact congrArg (fun p => p.2.1) named
  · have named := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      true false s v last
    cases congrArg Prod.fst named

/-- Two arclength-calibrated half-plane charts at a unique-mark slot fill a
whole ball in the full graft. The original cut surface may supply both sides. -/
theorem bankStack_bankSlot_hasMetricBallChart
    (slot : BankStackSlot stack) (t : Parameter slot.1) (param : Parameter slot.1 → ℝ)
    (nodup : ∀ e, (stack e).Nodup)
    (unique : BankStackUniqueMarksAt stack X base gap slot.1 t)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (positive : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (point X Banks (L slot t)) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1,
        Relation.EqvGen Banks (L slot t) ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r)
    {r₁ r₂ speed : ℝ}
    (left : BankHalfPlaneChart (bankStackLeftCurve stack X base gap slot) t false
      (fun s => (param s - param t) * speed) r₁)
    (right : BankHalfPlaneChart (bankStackRightCurve stack X base gap slot) t true
      (fun s => (param s - param t) * speed) r₂)
    (speed_pos : 0 < speed) (inside : param t ∈ interior (Set.range param))
    (lm : ∀ s, edist (bankStackLeftCurve stack X base gap slot t)
      (bankStackLeftCurve stack X base gap slot s) = ENNReal.ofReal (|param s - param t| * speed))
    (rm : ∀ s, edist (bankStackRightCurve stack X base gap slot t)
      (bankStackRightCurve stack X base gap slot s) = ENNReal.ofReal (|param s - param t| * speed)) :
    HasMetricBallChart ℂ (point X Banks (L slot t)) := by
  let lc := bankStackLeftCurve stack X base gap slot
  let rc := bankStackRightCurve stack X base gap slot
  let pair := bankPairGlue X lc rc
  let selected := bankStackSelectedSeams X stack base gap {slot}
  let x := point X pair ⟨_, lc t⟩
  have llabel (s : Parameter slot.1) := bankStackLeft_curve stack X base gap slot s
  have rlabel (s : Parameter slot.1) := bankStackRight_curve stack X base gap slot s
  have wrong_left (s : Parameter slot.1) : (⟨_, rc t⟩ : Total X) ≠ ⟨_, lc s⟩ := by
    intro h
    have equal := (llabel s).trans (h.symm.trans (rlabel t).symm)
    have sides := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      true false slot s equal
    cases congrArg Prod.fst sides
  have wrong_right (s : Parameter slot.1) : (⟨_, lc t⟩ : Total X) ≠ ⟨_, rc s⟩ := by
    intro h
    have equal := (rlabel s).trans (h.symm.trans (llabel t).symm)
    have sides := bankStackEndpoint_eq_of_unique stack X base gap nodup slot t unique
      false true slot s equal
    cases congrArg Prod.fst sides
  have planar := bankPair_planarBall_of_charts X lc rc t param left right speed_pos inside lm rm
    (bankStackLeftCurve_closed stack X base gap base_closed gap_closed slot).isClosed_range
    (bankStackRightCurve_closed stack X base gap base_closed gap_closed slot).isClosed_range
    wrong_left wrong_right
  have seams (p q : Total X) : pair p q ↔ selected p q := by
    constructor
    · rintro ⟨s, hp, hq⟩
      exact ⟨⟨slot, rfl⟩, s, hp.trans (llabel s).symm, hq.trans (rlabel s).symm⟩
    · rintro ⟨⟨other, h⟩, s, hp, hq⟩
      change other = slot at h
      subst other
      exact ⟨s, hp.trans (llabel s), hq.trans (rlabel s)⟩
  let E := changeSeamsIsometryEquiv X (R := pair) (S := selected)
    (fun p q h => point_eq_of_glue X ((seams p q).mp h))
    (fun p q h => point_eq_of_glue X ((seams p q).mpr h))
  have center : E x = point X selected (L slot t) :=
    congrArg (point X selected) (llabel t).symm
  have core : HasMetricBallChart ℂ (point X selected (L slot t)) :=
    center ▸ planar.isometryEquiv E
  obtain ⟨r, rpos, B, centered⟩ := bankStack_exists_single_forgetChart X stack base gap
    slot t nodup unique base_closed gap_closed positive cover
  exact core.of_centered_ball_equiv rpos B centered

end Unfoldings.MetricGluing
