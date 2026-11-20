module

public import Unfoldings.Cone.SectorCycleBall
public import Unfoldings.Metric.BankStackCyclicClass

/-! Whole planar balls at the actual cyclic classes of a finite bank stack. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

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
local notation "Next[" i "]" => finRotate (n + 1) i
local notation "Point" => point X Banks

variable (heading : Fin (n + 2) → ℝ)
  (origin : ∀ j, PolygonalPoint (placedAngularSector heading j)) {ρ : ℝ}
  (A : SectorCoverChart X H.center (placedAngularSector heading) origin ρ)

local notation "Ball[" j "]" => Metric.eball (Sigma.snd (H.center j)) (ENNReal.ofReal ρ)
local notation "Model[" j "]" => Metric.eball (origin j) (ENNReal.ofReal ρ)

private theorem modelTag_of_coordinate (j : Fin (n + 1)) (z : Model[j]) (x : Ball[j])
    (equal : (A.chart j x).val.val = z.val.val) :
    A.modelTag j z = A.patchTag j x := by
  have eq : A.chart j x = z := Subtype.ext (PolygonalPoint.ext equal)
  rw [← eq, SectorCoverChart.modelTag, (A.chart j).symm_apply_apply]

private theorem point_center (j : Fin (n + 1)) :
    Point (H.center 0) = Point (H.center j) :=
  point_eq_of_eqvGen X (H.related j)

/-- The actual slots of an ordered sector cycle give a whole planar graft ball when
their marked curves have the same exact length parameters at both adjacent charts. -/
theorem planarBall_of_marked_sectors
    (ordered : StrictMono heading) (start : heading 0 = 0)
    (finish : heading (Fin.last (n + 1)) = 2 * Real.pi)
    (width : ∀ i : Fin (n + 1), heading i.succ - heading i.castSucc < 2 * Real.pi)
    (time : Fin (n + 1) → unitInterval → Time)
    (length : Fin (n + 1) → ℝ) (fit : ∀ i, ρ ≤ length i)
    (before : ∀ i (t : unitInterval), t.val * length i < ρ → ∃ x : Ball[i],
      A.patchTag i x = EndAt (H.side i) (time i t).1 (time i t).2 ∧
      (A.chart i x).val.val = (t.val * length i) • polarRay (heading i.succ))
    (after : ∀ i (t : unitInterval), t.val * length i < ρ → ∃ x : Ball[Next[i]],
      A.patchTag Next[i] x = EndAt (!(H.side i)) (time i t).1 (time i t).2 ∧
      (A.chart Next[i] x).val.val = (t.val * length i) • polarRay (heading i.succ))
    (slots : ∀ s : Time, edist (Point (H.center 0)) (Point (L s.1 s.2)) < ENNReal.ofReal ρ →
      ∃ i t, s = time i t ∧ t.val * length i < ρ)
    (cover : ∀ b (r : ℝ), 0 < r → r ≤ ρ →
      edist (Point (H.center 0)) (Point b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks (H.center 0) ⟨b.1, c⟩ ∧
        edist c b.2 < ENNReal.ofReal r) :
    HasMetricBallChart ℂ (Point (H.center 0)) := by
  let coordinate (i : Fin (n + 1)) (t : unitInterval) :=
    (t.val * length i) • polarRay (heading i.succ)
  have joined (i : Fin (n + 1)) (t : unitInterval) :
      Point (EndAt (H.side i) (time i t).1 (time i t).2) =
        Point (EndAt (!(H.side i)) (time i t).1 (time i t).2) := by
    let s := time i t
    cases h : H.side i
    · exact point_eq_of_glue X (glue := Banks) ⟨s.1, s.2, rfl, rfl⟩
    · exact (point_eq_of_glue X (glue := Banks) ⟨s.1, s.2, rfl, rfl⟩).symm
  have end_coord (i : Fin (n + 1)) (t : unitInterval) (bound : t.val * length i < ρ)
      (flag : Bool) : A.coordinates (EndAt flag (time i t).1 (time i t).2) = coordinate i t := by
    by_cases same : flag = H.side i
    · subst flag
      obtain ⟨x, tagged, coord⟩ := before i t bound
      rw [← tagged, A.coordinates_tag]
      exact coord
    · have opposite : flag = !(H.side i) := by cases flag <;> cases h : H.side i <;> simp_all
      subst flag
      obtain ⟨x, tagged, coord⟩ := after i t bound
      rw [← tagged, A.coordinates_tag]
      exact coord
  have compatible (i j : Fin (n + 1)) (x : Ball[i]) (y : Ball[j])
      (seam : Banks (A.patchTag i x) (A.patchTag j y)) :
      (A.chart i x).val.val = (A.chart j y).val.val := by
    obtain ⟨s, t, l, r⟩ := seam
    have named : Point (A.patchTag i x) = Point (L s t) := congrArg Point l
    have near_i : edist (Point (H.center i)) (Point (A.patchTag i x)) < ENNReal.ofReal ρ :=
      (edist_of_le X Banks (H.center i).1 _ _).trans_lt ((edist_comm _ _).trans_lt x.property)
    have close : edist (Point (H.center 0)) (Point (L s t)) < ENNReal.ofReal ρ :=
      (congrArg₂ edist (point_center X stack base gap H i) named.symm).trans_lt near_i
    obtain ⟨k, u, name, bound⟩ := slots ⟨s, t⟩ close
    have one := end_coord k u bound false
    have two := end_coord k u bound true
    let f (flag : Bool) (p : Time) : ℂ := A.coordinates (EndAt flag p.1 p.2)
    change f false (time k u) = coordinate k u at one
    change f true (time k u) = coordinate k u at two
    have a : f false ⟨s, t⟩ = coordinate k u := name.symm ▸ one
    have b : f true ⟨s, t⟩ = coordinate k u := name.symm ▸ two
    rw [← A.coordinates_tag, ← A.coordinates_tag, l, r]
    exact a.trans b.symm
  have apex (i j : Fin (n + 1)) (z : Model[i]) (w : Model[j])
      (zero_z : z.val.val = 0) (zero_w : w.val.val = 0) :
      Point (A.modelTag i z) = Point (A.modelTag j w) := by
    have canonical (k : Fin (n + 1)) : (origin k).val = 0 :=
      edist_eq_zero.mp ((A.radial k (origin k)).symm.trans (edist_self _))
    have center_eq (k : Fin (n + 1)) (u : Model[k]) (zero : u.val.val = 0) :
        A.modelTag k u = H.center k := by
      have same : u = ⟨origin k, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩ :=
        Subtype.ext (PolygonalPoint.ext (zero.trans (canonical k).symm))
      exact (congrArg (A.modelTag k) same).trans (A.modelTag_origin k)
    rw [center_eq i z zero_z, center_eq j w zero_w]
    exact (point_center X stack base gap H i).symm.trans (point_center X stack base gap H j)
  have ray (i : Fin (n + 1)) (z : Model[i]) (w : Model[Next[i]]) (r : ℝ≥0)
      (at_ray : z.val.val = (r : ℂ) * polarRay (heading i.succ))
      (same : w.val.val = z.val.val) :
      Point (A.modelTag i z) = Point (A.modelTag Next[i] w) := by
    have distance : edist z.val.val (0 : ℂ) = ENNReal.ofReal (r : ℝ) := by
      rw [edist_dist, dist_zero_right, at_ray, norm_mul, norm_polarRay, mul_one,
        Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg]
    have bound : (r : ℝ) < ρ :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp
        ((distance.symm.trans (A.radial i z.val).symm).trans_lt z.property)
    have pos : 0 < length i := A.positive.trans_le (fit i)
    let t : unitInterval := ⟨r.val / length i, div_nonneg r.coe_nonneg pos.le,
      (div_le_one pos).mpr (bound.le.trans (fit i))⟩
    have scale : t.val * length i = r.val := div_mul_cancel₀ _ pos.ne'
    have small : t.val * length i < ρ := scale.trans_lt bound
    have coord : coordinate i t = z.val.val := by
      change (t.val * length i) • polarRay (heading i.succ) = _
      rw [scale, Complex.real_smul]
      exact at_ray.symm
    obtain ⟨x, left_tag, left_coord⟩ := before i t small
    obtain ⟨y, right_tag, right_coord⟩ := after i t small
    have mx := modelTag_of_coordinate X stack base gap H heading origin A i z x
      (left_coord.trans coord)
    have my := modelTag_of_coordinate X stack base gap H heading origin A Next[i] w y
      (right_coord.trans (coord.trans same.symm))
    rw [mx, my, left_tag, right_tag]
    exact joined i t
  have near_tags (b : Total X) (r : ℝ) (pos : 0 < r) (fit : r ≤ ρ)
      (near : edist (Point (H.center 0)) (Point b) < ENNReal.ofReal r) :
      ∃ (i : Fin (n + 1)) (x : Ball[i]),
        A.patchTag i x = b ∧ edist x.val (H.center i).2 < ENNReal.ofReal r := by
    obtain ⟨c, related, distance⟩ := cover b r pos fit near
    obtain ⟨i, same⟩ := (H.eqvGen_iff ⟨b.1, c⟩).mp related
    let P (a : Total X) :=
      ∃ x : Metric.eball a.2 (ENNReal.ofReal ρ),
        (⟨a.1, x.val⟩ : Total X) = b ∧ edist x.val a.2 < ENNReal.ofReal r
    have close := (edist_comm _ _).trans_lt distance
    have exists_tag : P ⟨b.1, c⟩ :=
      ⟨⟨b.2, close.trans_le (ENNReal.ofReal_le_ofReal fit)⟩, Sigma.eta b, close⟩
    obtain ⟨x, tag, small⟩ := (show P (H.center i) from same ▸ exists_tag)
    exact ⟨i, x, tag, small⟩
  exact A.hasMetricBallChart_of_angular_cycle X heading H.center origin ordered start finish
    width 0 apex ray compatible near_tags

end Unfoldings.MetricGluing.BankStackCyclicClass
