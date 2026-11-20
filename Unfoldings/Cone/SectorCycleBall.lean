module

public import Unfoldings.Cone.AngularSectorCycle
public import Unfoldings.Cone.SectorCoverBall
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Glue a whole metric ball using the exact common rays of a full ordered sector cycle. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing.SectorCoverChart

variable {I : Type*} {n : ℕ} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  {glue : Total X → Total X → Prop}
  (heading : Fin (n + 2) → ℝ) (center : Fin (n + 1) → Total X)
  (origin : ∀ j, PolygonalPoint (placedAngularSector heading j)) {ρ : ℝ}
  (A : SectorCoverChart X center (placedAngularSector heading) origin ρ)

local notation "Model[" j "]" => Metric.eball (origin j) (ENNReal.ofReal ρ)
local notation "Ball[" j "]" => Metric.eball (Sigma.snd (center j)) (ENNReal.ofReal ρ)
local notation "Next[" i "]" => finRotate (n + 1) i
local notation "Point" => point X glue

/-- A finite cyclic family of placed intrinsic charts glues a whole planar ball.
The only common coordinates to check are the apex and the actual successive rays. -/
theorem hasMetricBallChart_of_angular_cycle
    (ordered : StrictMono heading) (start : heading 0 = 0)
    (finish : heading (Fin.last (n + 1)) = 2 * Real.pi)
    (width : ∀ i : Fin (n + 1), heading i.succ - heading i.castSucc < 2 * Real.pi)
    (j₀ : Fin (n + 1))
    (apex : ∀ (i j : Fin (n + 1)) (z : Model[i]) (w : Model[j]),
      z.val.val = 0 → w.val.val = 0 → Point (A.modelTag i z) = Point (A.modelTag j w))
    (ray : ∀ (i : Fin (n + 1)) (z : Model[i]) (w : Model[Next[i]]) (r : ℝ≥0),
      z.val.val = (r : ℂ) * polarRay (heading i.succ) →
      w.val.val = z.val.val → Point (A.modelTag i z) = Point (A.modelTag Next[i] w))
    (compatible : ∀ (i j : Fin (n + 1)) (x : Ball[i]) (y : Ball[j]),
      glue (A.patchTag i x) (A.patchTag j y) → (A.chart i x).val.val = (A.chart j y).val.val)
    (near_tags : ∀ b (r : ℝ), 0 < r → r ≤ ρ →
      edist (Point (center j₀)) (Point b) < ENNReal.ofReal r →
      ∃ (j : Fin (n + 1)) (x : Ball[j]),
        A.patchTag j x = b ∧ edist x.val (center j).2 < ENNReal.ofReal r) :
    HasMetricBallChart ℂ (Point (center j₀)) := by
  let α (i : Fin (n + 1)) := heading i.castSucc
  let β (i : Fin (n + 1)) := heading i.succ
  let μ (i : Fin (n + 1)) := (α i + β i) / 2
  let Half := Fin (n + 1) × Bool
  let cell (p : Half) :=
    if p.2 then headingSector (α p.1) (μ p.1) else headingSector (μ p.1) (β p.1)
  have positive (i : Fin (n + 1)) : α i < β i := ordered Fin.castSucc_lt_succ
  have split (i : Fin (n + 1)) :
      placedAngularSector heading i = cell (i, true) ∪ cell (i, false) := by
    simpa only [cell, ite_true, Bool.false_eq_true, ite_false] using
      placedAngularSector_eq_convex_halves heading i (positive i) (width i)
  have inside (p : Half) : cell p ⊆ placedAngularSector heading p.1 := by
    obtain ⟨i, side⟩ := p
    rw [split i]
    cases side
    · exact Set.subset_union_right
    · exact Set.subset_union_left
  have closed (p : Half) : IsClosed (cell p) := by
    obtain ⟨i, side⟩ := p
    have h : β i - α i < 2 * Real.pi := width i
    cases side
    · change IsClosed (headingSector (μ i) (β i))
      exact isClosed_headingSector _ _ (by dsimp [μ]; linarith [positive i])
        (by dsimp [μ]; linarith)
    · change IsClosed (headingSector (α i) (μ i))
      exact isClosed_headingSector _ _ (by dsimp [μ]; linarith [positive i])
        (by dsimp [μ]; linarith)
  have convex (p : Half) : Convex ℝ (cell p) := by
    obtain ⟨i, side⟩ := p
    cases side <;> exact convex_headingSector _ _
  have cover (z : ℂ) (_ : z ∈ Metric.ball (0 : ℂ) ρ) : ∃ p : Half, z ∈ cell p := by
    obtain ⟨i, member⟩ := exists_mem_placedAngularSector heading start finish z
    rw [split] at member
    exact member.elim (fun h => ⟨(i, true), h⟩) (fun h => ⟨(i, false), h⟩)
  have cast_value {i j : Fin (n + 1)} (eq : i = j) (z : Model[i]) :
      ((eq ▸ z : Model[j]).val.val) = z.val.val := by
    cases eq
    rfl
  have cast_tag {i j : Fin (n + 1)} (eq : i = j) (z : Model[i]) :
      A.modelTag j (eq ▸ z) = A.modelTag i z := by
    cases eq
    rfl
  have shared_ordered (i j : Fin (n + 1)) (ij : i < j) (z : Model[i]) (w : Model[j])
      (equal : z.val.val = w.val.val) : Point (A.modelTag i z) = Point (A.modelTag j w) := by
    rcases placedAngularSector_shared heading ordered start finish ij z.val.property
        (equal.symm ▸ w.val.property) with zero | ⟨step, r, at_ray⟩ | ⟨h₀, h₁, r, at_ray⟩
    · exact apex i j z w zero (equal.symm.trans zero)
    · have before : i.val < n := ij.trans_le (Fin.le_last j)
      have named : Next[i] = j := by
        have index : i = (⟨i.val, before⟩ : Fin n).castSucc := Fin.ext rfl
        rw [index, show Next[(⟨i.val, before⟩ : Fin n).castSucc] =
          (⟨i.val, before⟩ : Fin n).succ from finRotate_of_lt before]
        exact Fin.ext (congrArg (fun k : Fin (n + 2) => k.val) step)
      subst j
      exact ray i z w r at_ray equal.symm
    · subst i
      subst j
      have tail : w.val.val = (r : ℂ) * polarRay (heading (Fin.last n).succ) := by
        rw [Fin.succ_last, finish]
        simpa [polarRay] using equal.symm.trans at_ray
      have next : Next[Fin.last n] = 0 := finRotate_last
      let w' : Model[Next[Fin.last n]] := next.symm ▸ z
      have hw : w'.val.val = z.val.val := cast_value next.symm z
      have related := (ray (Fin.last n) w w' r tail (hw.trans equal)).symm
      have same : A.modelTag Next[Fin.last n] w' = A.modelTag 0 z := cast_tag next.symm z
      exact (congrArg Point same).symm.trans related
  have shared (i j : Fin (n + 1)) (z : Model[i]) (w : Model[j])
      (equal : z.val.val = w.val.val) : Point (A.modelTag i z) = Point (A.modelTag j w) := by
    rcases lt_trichotomy i j with before | rfl | after
    · exact shared_ordered i j before z w equal
    · have same : z = w := Subtype.ext (PolygonalPoint.ext equal)
      rw [same]
    · exact (shared_ordered j i after w z equal.symm).symm
  exact A.hasMetricBallChart cell Prod.fst inside j₀ closed convex cover shared compatible near_tags

end Unfoldings.MetricGluing.SectorCoverChart
