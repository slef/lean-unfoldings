module

public import Unfoldings.Cone.SectorCoverBall
public import Unfoldings.Metric.Barrier
public import Unfoldings.Metric.Unglued

/-! Distinct original centers of a finite sector family admit a common separation radius. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I J : Type*} [Finite J] (X : I → Type*) [∀ i, EMetricSpace (X i)]
  (center : J → Total X)

private theorem faceCost_centers_pos (unique : Function.Injective center) {j k : J}
    (distinct : j ≠ k) : 0 < faceCost X (center j) (center k) := by
  classical
  have sep : center j ≠ center k := fun h => distinct (unique h)
  rcases hi : center j with ⟨i, x⟩
  rcases hl : center k with ⟨l, y⟩
  rw [hi, hl] at sep
  unfold faceCost
  dsimp
  split
  · rename_i same
    subst l
    exact pos_iff_ne_zero.mpr (fun zero => sep (congrArg (Sigma.mk i) (edist_eq_zero.mp zero)))
  · exact lt_trans zero_lt_one ENNReal.one_lt_top

/-- A sufficiently small radius separates any pair of original sector balls from
different copies in the same metric piece. -/
theorem exists_sectorCover_separationRadius (unique : Function.Injective center) :
    ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ →
      ∀ (j k : J), j ≠ k → ∀ (tag : (center j).1 = (center k).1)
        (x : Metric.eball (center j).2 (ENNReal.ofReal ρ))
        (y : Metric.eball (center k).2 (ENNReal.ofReal ρ)),
        ENNReal.ofReal (2 * ρ) ≤ edist (tag ▸ x.val) y.val := by
  classical
  let D (p : J × J) := if p.1 = p.2 then 1 else
    (min 1 (faceCost X (center p.1) (center p.2))).toReal
  have Dpos (p : J × J) : 0 < D p := by
    unfold D
    split
    · exact zero_lt_one
    · rename_i diff
      exact ENNReal.toReal_pos
        (lt_min zero_lt_one (faceCost_centers_pos X center unique diff)).ne'
        ((min_le_left _ _).trans_lt ENNReal.one_lt_top).ne
  obtain ⟨ε, εpos, bound⟩ := MetricBarrier.exists_pos_le_of_finite D Dpos
  refine ⟨ε / 4, div_pos εpos (by norm_num), ?_⟩
  intro ρ positive small j k distinct tag x y
  have length : 4 * ρ ≤ D (j, k) := by linarith [bound (j, k)]
  have large : ENNReal.ofReal (4 * ρ) ≤ faceCost X (center j) (center k) := by
    apply (ENNReal.ofReal_le_ofReal length).trans
    simp only [D, ite_eq_right distinct]
    rw [ENNReal.ofReal_toReal ((min_le_left _ _).trans_lt ENNReal.one_lt_top).ne]
    exact min_le_right _ _
  let a : Total X := ⟨(center j).1, x.val⟩
  let b : Total X := ⟨(center k).1, y.val⟩
  have cost₁ : faceCost X (center j) a = edist (center j).2 x.val := by
    change faceCost X ⟨(center j).1, (center j).2⟩ a = _
    simp [a, faceCost]
  have cost₂ : faceCost X b (center k) = edist y.val (center k).2 := by
    change faceCost X b ⟨(center k).1, (center k).2⟩ = _
    simp [b, faceCost]
  have middle : faceCost X a b = edist (tag ▸ x.val) y.val := by
    change faceCost X ⟨(center j).1, x.val⟩ ⟨(center k).1, y.val⟩ = _
    rw [faceCost, dite_eq_left tag]
  by_contra! short
  have s₁ : faceCost X (center j) a < ENNReal.ofReal ρ :=
    cost₁.trans_lt ((edist_comm _ _).trans_lt x.property)
  have s₂ : faceCost X a b < ENNReal.ofReal (2 * ρ) := middle.trans_lt short
  have s₃ : faceCost X b (center k) < ENNReal.ofReal ρ := cost₂.trans_lt y.property
  have total := ENNReal.add_lt_add s₁ (ENNReal.add_lt_add s₂ s₃)
  have scale : ENNReal.ofReal ρ + (ENNReal.ofReal (2 * ρ) + ENNReal.ofReal ρ) =
      ENNReal.ofReal (4 * ρ) := by
    rw [← ENNReal.ofReal_add (by positivity) positive.le,
      ← ENNReal.ofReal_add positive.le (by positivity)]
    congr 1
    ring
  have estimates := (faceCost_triangle X (center j) a (center k)).trans
    (add_le_add le_rfl (faceCost_triangle X a b (center k)))
  exact (not_lt_of_ge large) (estimates.trans_lt (total.trans_eq scale))

end Unfoldings.MetricGluing
