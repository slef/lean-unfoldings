module

public import Unfoldings.Cone.SectorPairBankRays
public import Unfoldings.Cone.SectorPairOriginalClass
public import Unfoldings.Metric.BankStackLocalClasses

/-! Named slots and calibrated rays turn an original bank-stack pair into a whole planar ball. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing.SectorPairChart

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "End" => bankStackEndpoint stack X base gap
local notation "L" => bankStackLeft X stack base gap
local notation "Rgt" => bankStackRight X stack base gap
local notation "Banks" => bankSeams L Rgt
local notation "Time" => (Σ s : BankStackSlot stack, Parameter (Sigma.fst s))
local notation "Point" => point X Banks

variable {a : Bool → Total X} {θ : ℝ} {pos : 0 < θ} {small : θ < 2 * Real.pi} {ρ : ℝ}

local notation "tag" => pairTag a (r := ENNReal.ofReal ρ)

/-- Two original sector charts fill a whole graft ball when all nearby seams are
named by their calibrated original rays and the center class has exactly two marks. -/
theorem bankStack_planarBall
  (A : SectorPairChart X a pos small ρ) (first : Time)
  (lc : L first.1 first.2 = a false) (rc : Rgt first.1 first.2 = a true)
  (mark : ∀ b : Bool, Bool → unitInterval → X (a b).1)
  (time : Bool → unitInterval → Time)
  (seam_ends : ∀ b ray t, End b (time ray t).1 (time ray t).2 = ⟨(a b).1, mark b ray t⟩)
  (length : Bool → ℝ) (length_fit : ∀ ray, ρ ≤ length ray)
    (distance : ∀ b ray t, edist (mark b ray t) (a b).2 = ENNReal.ofReal (t.val * length ray))
    (coords : ∀ b ray t (near : edist (mark b ray t) (a b).2 < ENNReal.ofReal ρ),
      (A.chart b ⟨mark b ray t, near⟩).val.val = bankRay θ ray (t.val * length ray))
    (slots : ∀ p : Time,
      edist (Point (L first.1 first.2)) (Point (L p.1 p.2)) < ENNReal.ofReal ρ →
        ∃ ray t, p = time ray t)
    {ε : ℝ} (fit : ρ ≤ ε)
    (class_eq : ∀ z, Relation.EqvGen Banks (L first.1 first.2) z →
      z = L first.1 first.2 ∨ z = Rgt first.1 first.2)
    (cover : ∀ r, 0 < r → r ≤ ε → ∀ b : Total X,
      edist (Point (L first.1 first.2)) (Point b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks (L first.1 first.2) ⟨b.1, c⟩ ∧
        edist c b.2 < ENNReal.ofReal r) :
    HasMetricBallChart ℂ (Point (L first.1 first.2)) := by
  have center (b : Bool) : Point (L first.1 first.2) = Point (a b) := by
    cases b
    · exact congrArg Point lc
    · exact (point_eq_of_glue X ⟨first.1, first.2, rfl, rfl⟩).trans (congrArg Point rc)
  have joined (ray : Bool) (t : unitInterval) :
      Point ⟨(a false).1, mark false ray t⟩ = Point ⟨(a true).1, mark true ray t⟩ := by
    let p := time ray t
    exact (congrArg Point (seam_ends false ray t)).symm.trans
      ((point_eq_of_glue X ⟨p.1, p.2, rfl, rfl⟩).trans (congrArg Point (seam_ends true ray t)))
  have compatible (b c : Bool) (x : Metric.eball (a b).2 (ENNReal.ofReal ρ))
      (y : Metric.eball (a c).2 (ENNReal.ofReal ρ)) (seam : Banks (tag b x) (tag c y)) :
      (A.chart b x).val.val = (A.chart c y).val.val := by
    obtain ⟨s, t, l, r⟩ := seam
    have named : Point (tag b x) = Point (L s t) := congrArg Point l
    have bound : edist (Point (L first.1 first.2)) (Point (L s t)) < ENNReal.ofReal ρ := by
      have near := (edist_of_le X Banks (a b).1 (a b).2 x.val).trans_lt
        ((edist_comm _ _).trans_lt x.property)
      exact (congrArg₂ edist (center b) named.symm).trans_lt near
    obtain ⟨ray, u, name⟩ := slots ⟨s, t⟩ bound
    have left : tag b x = ⟨(a false).1, mark false ray u⟩ :=
      l.trans ((congrArg (fun p : Time => L p.1 p.2) name).trans (seam_ends false ray u))
    have right : tag c y = ⟨(a true).1, mark true ray u⟩ :=
      r.trans ((congrArg (fun p : Time => Rgt p.1 p.2) name).trans (seam_ends true ray u))
    exact (A.chart_eq_of_tag b false x (mark false ray u) (coords false ray u) left).trans
      (A.chart_eq_of_tag c true y (mark true ray u) (coords true ray u) right).symm
  have class_at (z : Total X) (related : Relation.EqvGen Banks (a false) z) :
      z = a false ∨ z = a true :=
    (class_eq z (lc.symm ▸ related)).imp (fun h => h.trans lc) (fun h => h.trans rc)
  have cover_at := covers_of_original_class (glue := Banks) (a := a) fit class_at (by
    intro r pos tight z near
    obtain ⟨c, related, close⟩ := cover r pos tight z (lc.symm ▸ near)
    exact ⟨c, lc ▸ related, close⟩)
  have chart := A.hasMetricBallChart compatible
    (A.shared_of_bankRays_lengths mark length length_fit distance coords joined) cover_at
  exact (center false).symm ▸ chart

end Unfoldings.MetricGluing.SectorPairChart
