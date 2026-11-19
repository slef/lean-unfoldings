module

public import Unfoldings.Cone.SectorPairBall

/-! Exact original center classes provide the full piece coverage needed by the sector chart. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing.SectorPairChart

variable {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {glue : Total X → Total X → Prop} {a : Bool → Total X}
  {θ : ℝ} {pos : 0 < θ} {small : θ < 2 * Real.pi} {R : ℝ}

private theorem near_tag {r ρ : ℝ} (small : r ≤ ρ) (b c : Total X)
    (tag : c.1 = b.1) (distance : edist (tag ▸ c.2) b.2 < ENNReal.ofReal r) :
    ∃ x : Metric.eball c.2 (ENNReal.ofReal ρ),
      (⟨c.1, x.val⟩ : Total X) = b ∧ edist x.val c.2 < ENNReal.ofReal r := by
  obtain ⟨i, b⟩ := b
  obtain ⟨j, c⟩ := c
  change j = i at tag
  subst j
  have near := (edist_comm _ _).trans_lt distance
  exact ⟨⟨b, near.trans_le (ENNReal.ofReal_le_ofReal small)⟩, rfl, near⟩

/-- Any smaller positive radius retains the same exact two original piece balls. -/
theorem covers_of_original_class {ε : ℝ} (fit : R ≤ ε)
    (class_eq : ∀ z, Relation.EqvGen glue (a false) z → z = a false ∨ z = a true)
    (cover : ∀ r, 0 < r → r ≤ ε → ∀ b : Total X,
      edist (point X glue (a false)) (point X glue b) < ENNReal.ofReal r →
      ∃ c : X b.1,
        Relation.EqvGen glue (a false) ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r) :
    ∀ (r : ℝ), r ≤ R → ∀ b : Total X,
      edist (point X glue b) (point X glue (a false)) < ENNReal.ofReal r →
      ∃ (side : Bool) (x : Metric.eball (a side).2 (ENNReal.ofReal R)),
        pairTag a side x = b ∧ edist x.val (a side).2 < ENNReal.ofReal r := by
  intro r tight b near
  have rpos : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le near)
  obtain ⟨c, belongs, close⟩ := cover r rpos (tight.trans fit) b
    ((edist_comm _ _).trans_lt near)
  have side_known : ∃ side, (⟨b.1, c⟩ : Total X) = a side := by
    rcases class_eq ⟨b.1, c⟩ belongs with left | right
    · exact ⟨false, left⟩
    · exact ⟨true, right⟩
  obtain ⟨side, equal⟩ := side_known
  let pack (z : Total X) :=
    ∃ x : Metric.eball z.2 (ENNReal.ofReal R),
      (⟨z.1, x.val⟩ : Total X) = b ∧ edist x.val z.2 < ENNReal.ofReal r
  have at_center : pack (a side) := equal ▸ near_tag tight b ⟨b.1, c⟩ rfl close
  obtain ⟨x, named, radial⟩ := at_center
  exact ⟨side, x, named, radial⟩

/-- The coordinate of a named mark can be used for any representative of the same tag. -/
theorem chart_eq_of_tag (A : SectorPairChart X a pos small R)
    (b c : Bool) (x : Metric.eball (a b).2 (ENNReal.ofReal R))
    (z : X (a c).1) {w : ℂ} (coords : ∀ hz : edist z (a c).2 < ENNReal.ofReal R,
      (A.chart c ⟨z, hz⟩).val.val = w)
    (equal : pairTag a b x = ⟨(a c).1, z⟩) : (A.chart b x).val.val = w := by
  have tags := congrArg (fun q : Total X => q.1) equal
  have same : b = c := by
    cases b <;> cases c
    · rfl
    · exact (A.distinct tags).elim
    · exact (A.distinct tags.symm).elim
    · rfl
  subst c
  have value := eq_of_heq (Sigma.mk.inj equal).2
  have near : edist z (a b).2 < ENNReal.ofReal R :=
    (congrArg (edist · (a b).2) value).symm.trans_lt x.property
  exact (congrArg (fun y => (A.chart b y).val.val) (Subtype.ext value)).trans (coords near)

end Unfoldings.MetricGluing.SectorPairChart
