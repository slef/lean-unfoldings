module

public import Unfoldings.Cone.MarkedSectorGerm
public import Unfoldings.Cone.SectorCycleBankStack

/-! Glue an actual cyclic bank-stack fan from its normalized marked original sectors. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.BankStackCyclicClass

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  {n : ℕ} (H : BankStackCyclicClass X stack base gap n)

local notation "L" => bankStackLeft X stack base gap
local notation "Rgt" => bankStackRight X stack base gap
local notation "EndAt" => bankStackEndpoint stack X base gap
local notation "Banks" => bankSeams L Rgt
local notation "Time" => (Σ slot : BankStackSlot stack, Parameter (Sigma.fst slot))
local notation "Next[" j "]" => finRotate (n + 1) j
local notation "Prev[" j "]" => Equiv.symm (finRotate (n + 1)) j
local notation "Point" => point X Banks
local notation "Curve" => bankStackLeftCurve stack X base gap

/-- One marked normalized chart for each named center, with literal bank slots on both sides. -/
structure MarkedAtlas where
  heading : Fin (n + 2) → ℝ
  ordered : StrictMono heading
  start : heading 0 = 0
  finish : heading (Fin.last (n + 1)) = 2 * Real.pi
  width (i : Fin (n + 1)) : heading i.succ - heading i.castSucc < 2 * Real.pi
  parameterize (i : Fin (n + 1)) : unitInterval ≃ Parameter (H.time i).1.1
  at_zero (i : Fin (n + 1)) : parameterize i 0 = (H.time i).2
  length : Fin (n + 1) → ℝ
  length_pos (i : Fin (n + 1)) : 0 < length i
  metric (i : Fin (n + 1)) (t : unitInterval) :
    edist (Curve (H.time i).1 (parameterize i 0)) (Curve (H.time i).1 (parameterize i t)) =
      ENNReal.ofReal (t.val * length i)
  reflected : Fin (n + 1) → Bool
  mark (i : Fin (n + 1)) : Bool → unitInterval → X (H.center i).1
  before (i : Fin (n + 1)) (t : unitInterval) :
    EndAt (H.side i) (H.time i).1 (parameterize i t) = ⟨(H.center i).1, mark i (!(reflected i)) t⟩
  after (i : Fin (n + 1)) (t : unitInterval) :
    EndAt (!(H.side i)) (H.time i).1 (parameterize i t) =
      ⟨(H.center (Next[i])).1, mark (Next[i]) (reflected (Next[i])) t⟩
  germ (i : Fin (n + 1)) :
    MarkedSectorGerm (H.center i).2 (heading i.succ - heading i.castSucc) (mark i)
      (fun b => if b = reflected i then length (Prev[i]) else length i)

namespace MarkedAtlas

variable {X stack base gap H} (A : MarkedAtlas X stack base gap H)

private theorem following_ray (i : Fin (n + 1)) :
    polarRay (A.heading (Next[i]).castSucc) = polarRay (A.heading i.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last, Fin.castSucc_zero, A.start, Fin.succ_last, A.finish]
    simp [polarRay]
  · have next : Next[j.castSucc] = j.succ := finRotate_of_lt j.isLt
    rw [next]
    congr 2

include A in
/-- Match the calibrated bank rays and construct a whole planar ball of the actual
route metric. No Euclidean placement of the complete stack pieces is needed. -/
theorem hasMetricBallChart [Finite Edge] [∀ e, TopologicalSpace (Parameter e)]
    (distinct : Function.Injective H.center)
    (base_closed : ∀ e side, Topology.IsClosedEmbedding (base e side))
    (gap_closed : ∀ e g h side, Topology.IsClosedEmbedding (gap e g h side))
    {R : ℝ} (Rpos : 0 < R)
    (cover : ∀ r, 0 < r → r ≤ R → ∀ b : Total X,
      edist (Point (H.center 0)) (Point b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks (H.center 0) ⟨b.1, c⟩ ∧
        edist c b.2 < ENNReal.ofReal r) :
    HasMetricBallChart ℂ (Point (H.center 0)) := by
  have classes (i : Option G) : {c : X i | Relation.EqvGen Banks (H.center 0) ⟨i, c⟩}.Finite := by
    have same : {c : X i | Relation.EqvGen Banks (H.center 0) ⟨i, c⟩} =
        (fun c : X i => (⟨i, c⟩ : Total X)) ⁻¹' Set.range H.center := by
      ext c
      exact (H.eqvGen_iff _).trans (exists_congr (fun _ => eq_comm))
    rw [same]
    exact Set.Finite.preimage (f := fun c : X i => (⟨i, c⟩ : Total X))
      (fun _ _ _ _ equal => eq_of_heq (Sigma.mk.inj equal).2) (Set.finite_range H.center)
  obtain ⟨δ, δpos, small_R, slot_near⟩ := exists_bankStack_incident_slot_radius_le X stack base gap
    (H.center 0) classes base_closed gap_closed Rpos cover
  obtain ⟨sep, sep_pos, separated⟩ := exists_sectorCover_separationRadius X H.center distinct
  obtain ⟨r, rpos, radii⟩ := MetricBarrier.exists_pos_le_of_finite
    (fun i => (A.germ i).sector.radius) (fun i => (A.germ i).sector.radius_pos)
  obtain ⟨l, lpos, lengths⟩ := MetricBarrier.exists_pos_le_of_finite A.length A.length_pos
  let ρ := min (min δ sep) (min r l)
  have ρpos : 0 < ρ := lt_min (lt_min δpos sep_pos) (lt_min rpos lpos)
  have clearance : ρ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have sep_small : ρ ≤ sep := (min_le_left _ _).trans (min_le_right _ _)
  have fit_radius (j : Fin (n + 1)) : ρ ≤ (A.germ j).sector.radius :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (radii j))
  have fit_length (j : Fin (n + 1)) : ρ ≤ A.length j :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (lengths j))
  let G (j : Fin (n + 1)) := (A.germ j).sector
  let placed := SectorCoverChart.ofCenteredSectors X A.heading H.center A.reflected
    (fun j => (G j).angle_pos.le) (fun j => (G j).radius) (fun j => (G j).radius_pos)
    (fun j => (G j).chart) (fun j => (G j).centered) ρpos fit_radius
      (separated ρ ρpos sep_small)
  let lengthAt (j : Fin (n + 1)) (b : Bool) := if b = A.reflected j then A.length (Prev[j])
    else A.length j
  have length_pos (j : Fin (n + 1)) (b : Bool) : 0 < lengthAt j b := by
    unfold lengthAt
    split <;> exact A.length_pos _
  let Ball (j : Fin (n + 1)) := Metric.eball (H.center j).2 (ENNReal.ofReal ρ)
  have sample (j : Fin (n + 1)) (b : Bool) (t : unitInterval)
      (near : t.val * lengthAt j b < ρ) :
      ∃ x : Ball j, placed.patchTag j x = ⟨(H.center j).1, A.mark j b t⟩ ∧
        (placed.chart j x).val.val =
          (t.val * lengthAt j b) • polarRay
            (if b = A.reflected j then A.heading j.castSucc else A.heading j.succ) := by
    have nonnegative : 0 ≤ t.val * lengthAt j b := mul_nonneg t.property.1 (length_pos j b).le
    have close : edist (A.mark j b t) (H.center j).2 < ENNReal.ofReal ρ :=
      ((A.germ j).distance b t).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg nonnegative).mpr near)
    let x : Ball j := ⟨A.mark j b t, close⟩
    refine ⟨x, rfl, ?_⟩
    exact placeCenteredSectorChart_bankRay A.heading j (A.reflected j) (H.center j).2
      (G j).angle_pos.le (ENNReal.ofReal_pos.mpr (G j).radius_pos)
      (ENNReal.ofReal_le_ofReal (fit_radius j)) (G j).chart (G j).centered x b nonnegative
      ((A.germ j).trace b t _)
  let time (j : Fin (n + 1)) (t : unitInterval) : Time :=
    ⟨(H.time j).1, A.parameterize j t⟩
  have before (j : Fin (n + 1)) (t : unitInterval) (near : t.val * A.length j < ρ) :
      ∃ x : Ball j, placed.patchTag j x = EndAt (H.side j) (time j t).1 (time j t).2 ∧
        (placed.chart j x).val.val = (t.val * A.length j) • polarRay (A.heading j.succ) := by
    have opposite : (!(A.reflected j)) ≠ A.reflected j := by cases A.reflected j <;> decide
    have len : lengthAt j (!(A.reflected j)) = A.length j := ite_eq_right opposite
    obtain ⟨x, tag, coord⟩ := sample j (!(A.reflected j)) t (len.symm ▸ near)
    refine ⟨x, tag.trans (A.before j t).symm, ?_⟩
    simpa only [len, ite_eq_right opposite] using coord
  have after (j : Fin (n + 1)) (t : unitInterval) (near : t.val * A.length j < ρ) :
      ∃ x : Ball (Next[j]), placed.patchTag Next[j] x =
        EndAt (!(H.side j)) (time j t).1 (time j t).2 ∧
        (placed.chart Next[j] x).val.val = (t.val * A.length j) • polarRay (A.heading j.succ) := by
    let k := Next[j]
    have len : lengthAt k (A.reflected k) = A.length j := by
      simp only [lengthAt, ite_eq_left rfl, k, Equiv.symm_apply_apply]
    obtain ⟨x, tag, coord⟩ := sample k (A.reflected k) t (len.symm ▸ near)
    refine ⟨x, tag.trans (A.after j t).symm, ?_⟩
    simpa only [len, ite_eq_left rfl, ite_true, k, A.following_ray j] using coord
  have slots (s : Time) (near : edist (Point (H.center 0)) (Point (L s.1 s.2)) <
      ENNReal.ofReal ρ) : ∃ i t, s = time i t ∧ t.val * A.length i < ρ := by
    apply H.exists_near_marked_slot A.parameterize A.at_zero A.length
      (fun i => (A.length_pos i).le) A.metric _ s near
    intro u close
    exact slot_near ρ ρpos clearance u.1 u.2 close
  exact H.planarBall_of_marked_sectors X stack base gap A.heading _ placed A.ordered
    A.start A.finish A.width time A.length fit_length before after slots
      (fun b ε pos short near => cover ε pos (short.trans (clearance.trans small_R)) b near)

end MarkedAtlas

end Unfoldings.MetricGluing.BankStackCyclicClass
