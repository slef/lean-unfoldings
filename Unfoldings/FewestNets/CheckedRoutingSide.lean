module

public import Unfoldings.Convex.FiniteVisualHistoryCone
public import Unfoldings.FewestNets.CheckedExteriorSide
public import Unfoldings.FewestNets.CheckedVisualUpperPanel

/-! The combined finite certificate for a side of a routing cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

structure RoutingSideWitness (V : ℕ) where
  lower : List (SideVisualWitness V)
  upper : List (UpperVisualPanel V)
  exterior : Fin V × Fin V

variable {D V : ℕ} (hD : 0 < D) {a b n : Plane} {body : Fin V → Plane}
  (ca : CheckedPlane D a) (cb : CheckedPlane D b) (cn : CheckedPlane D n)
  (vertices : ∀ i, CheckedPlane D (body i))

/-- Every listed body vertex lies strictly inside the given support line. -/
def checkBodySide {offset : ℝ} (co : CheckedReal D offset) : Bool :=
  (List.finRange V).all fun i => (CheckedPlane.dot hD cn (vertices i)).isLT co

theorem progressBody_strictSide_of_check {offset : ℝ} (co : CheckedReal D offset)
    (passed : checkBodySide hD cn vertices co = true) :
    convexHull ℝ (Set.range body) ⊆ {q | inner ℝ n q < offset} := by
  apply convexHull_min _ (convex_halfSpace_lt (innerSL ℝ n).toLinearMap.isLinear _)
  rintro _ ⟨i, rfl⟩
  exact CheckedReal.lt_of_isLT hD _ _ (List.all_eq_true.mp passed i (List.mem_finRange i))

/-- Check all three geometric routing margins on the fully closed side. -/
def checkRoutingSide (next : Equiv.Perm (Fin V)) {offset cot γ : ℝ}
    (co : CheckedReal D offset) (cc : CheckedReal D cot) (cg : CheckedReal D γ)
    (w : RoutingSideWitness V) : Bool :=
  checkBodySide hD cn vertices co &&
    SideVisualWitness.coversFrom 0 w.lower &&
    w.lower.all (SideVisualWitness.checkPanel hD cc ca cb vertices) &&
    coversRationalPanels UpperVisualPanel.endpoints 0 w.upper &&
    w.upper.all (UpperVisualPanel.checkConvex hD next cc ca cb vertices) &&
    checkExteriorWitness hD true cn ca cb (vertices w.exterior.1) cg &&
    checkExteriorWitness hD false cn ca cb (vertices w.exterior.2) cg

/-- The whole-side check gives the angular width of the actual history cone
and the polar margin for every direction in it. -/
theorem routingCone_of_check [Nonempty (Fin V)] {next : Equiv.Perm (Fin V)}
    (convex : CyclicConvexVertices body next) (distinct : Function.Injective body)
    {θ cot γ offset : ℝ} (co : CheckedReal D offset) (cc : CheckedReal D cot)
    (cg : CheckedReal D γ)
    (angle_pos : 0 < θ) (angle_small : θ ≤ π / 2) (cot_nonneg : 0 ≤ cot)
    (cot_bound : cot * sin θ < cos θ) (margin_nonneg : 0 ≤ γ) (unit : ‖n‖ = 1)
    (w : RoutingSideWitness V) (passed : checkRoutingSide hD ca cb cn vertices next co cc cg w = true)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let p := AffineMap.lineMap a b t
    let L := convexHull ℝ (Set.range body)
    offset ≤ inner ℝ n p →
      (∃ axis : Plane, ∃ width : ℝ, axis ≠ 0 ∧ θ < width ∧ width < π - θ ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) ∧
      ∀ z : Plane, z ∈ SlopeEnvelope.historyCone L p → γ * ‖z‖ ≤ inner ℝ n z := by
  dsimp only
  intro line
  unfold checkRoutingSide at passed
  simp only [Bool.and_eq_true] at passed
  obtain ⟨⟨⟨⟨⟨⟨in_side, lower_cover⟩, lower_pass⟩, upper_cover⟩, upper_pass⟩,
    exterior_first⟩, exterior_last⟩ := passed
  let p := AffineMap.lineMap a b t
  have inside (i : Fin V) : 0 < inner ℝ n (p - body i) := by
    rw [inner_sub_right]
    have strict := CheckedReal.lt_of_isLT hD _ _
      (List.all_eq_true.mp in_side i (List.mem_finRange i))
    exact sub_pos.mpr (strict.trans_le line)
  have lower_nonempty : w.lower ≠ [] := by
    intro empty
    simp [empty, SideVisualWitness.coversFrom, coversRationalPanels] at lower_cover
  have upper_nonempty : w.upper ≠ [] := by
    intro empty
    simp [empty, coversRationalPanels] at upper_cover
  have lower := SideVisualWitness.lowerVisualAngle_of_check hD angle_pos angle_small cot_nonneg
    cot_bound cc ca cb vertices w.lower lower_nonempty lower_cover lower_pass ht
  have upper (i j : Fin V) (_ : i ≠ j) : angle (p - body i) (p - body j) < π - θ :=
    UpperVisualPanel.angle_lt_of_checked_convex_cover hD convex distinct cc ca cb vertices
      angle_pos angle_small cot_nonneg cot_bound w.upper upper_nonempty upper_cover upper_pass ht i j
  constructor
  · obtain ⟨axis, width, nz, lo, hi, cone⟩ :=
      SlopeEnvelope.exists_historyCone_angle_of_vertex_bounds body p n inside angle_pos.le
        (sub_le_self π angle_pos.le) lower upper
    exact ⟨axis, width, nz, by linarith only [lo], hi, cone⟩
  · intro z history
    have cone (i : Fin V) : 0 ≤ inner ℝ (p - body i) z := by
      rw [inner_sub_left, sub_nonneg]
      exact history (body i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    obtain ⟨d₁, positive₁, upper₁, signed₁, ratio₁⟩ := exteriorWitness_of_check hD true
      cn ca cb (vertices w.exterior.1) cg exterior_first ht
    obtain ⟨d₂, positive₂, upper₂, signed₂, ratio₂⟩ := exteriorWitness_of_check hD false
      cn ca cb (vertices w.exterior.2) cg exterior_last ht
    simp only [SideVisualWitness.signedCot, Bool.false_eq_true, ite_false] at signed₂
    exact exterior_margin_of_witnesses certificateOrientation unit margin_nonneg d₁ d₂
      positive₁ positive₂ upper₁ upper₂ signed₁ (le_neg_of_le_neg signed₂)
      (cone w.exterior.1) (cone w.exterior.2) ratio₁ ratio₂

end Unfoldings.FewestNets
