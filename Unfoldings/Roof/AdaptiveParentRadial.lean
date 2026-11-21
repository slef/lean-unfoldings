module

public import Unfoldings.Roof.CompatibleAdaptivePaths

/-! The actual attached adaptive parent links have certified radial progress. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatibleAdaptiveRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {L : Set Plane} {r margin η : ℝ} (R : K.CompatibleAdaptiveRouting U G boundary L r margin η)

/-- The routed direction at an actual parent step has the same radial margin
after any partial step. An exterior parent uses the ray's first contact. -/
theorem parent_radial_margin {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (interior_margin : γ ≤ margin) (exterior_margin : γ ≤ η)
    {q : Plane} {v : C.Vertex Set.univ} (nonterminal : v ∉ R.parents.roots)
    (history : (G.boundaryEnvelope boundary).HistoryProgress L q (K.projectedVertex v))
    {s : ℝ} (time : 0 ≤ s) :
    let x := K.projectedVertex v
    let d := K.projectedVertex (R.parents.parent v) - x
    γ * (‖x + s • d - q‖ * ‖d‖) ≤ inner ℝ (x + s • d - q) d := by
  let x := K.projectedVertex v
  let d := K.projectedVertex (R.parents.parent v) - x
  change γ * (‖x + s • d - q‖ * ‖d‖) ≤ inner ℝ (x + s • d - q) d
  by_cases root : v ∈ R.original.parents.roots
  · let w : {w // w ∈ R.original.parents.roots} := ⟨v, root⟩
    let u := R.exterior.direction (R.exterior.slope w)
    have not_terminal : w ∉ R.exterior.parents.roots := fun h => nonterminal ⟨root, h⟩
    have parent_eq : R.parents.parent v = (R.exterior.parents.parent w).val :=
      R.original.parents.attach_parent_root R.exterior.parents R.shared_height w
    obtain ⟨t, positive, contact⟩ := (R.exterior.next_spec not_terminal).1
    have point : R.exterior.point w = x := R.exterior_points w
    have step : d = t • u := by
      change K.projectedVertex (R.parents.parent v) - x = _
      rw [parent_eq, ← R.exterior_points]
      change R.exterior.point (R.exterior.next w) - x = _
      rw [contact]
      change R.exterior.point w + t • u - x = _
      rw [point, add_sub_cancel_left]
    have history' : (G.boundaryEnvelope boundary).HistoryProgress L q (R.exterior.point w) :=
      point.symm ▸ history
    have polar (z : Plane) (hz : z ∈ SlopeEnvelope.historyCone L (R.exterior.slope w)) :
        γ * ‖z‖ ≤ inner ℝ z u :=
      (mul_le_mul_of_nonneg_right exterior_margin (norm_nonneg z)).trans (R.exterior_polar w z hz)
    have radial := R.exterior.radial_margin_ray boundary w nonnegative small polar history'
      (t := s * t) (mul_nonneg time positive.le)
    change γ * ‖R.exterior.point w + (s * t) • u - q‖ ≤
      inner ℝ (R.exterior.point w + (s * t) • u - q) u at radial
    rw [point, ← smul_smul] at radial
    have norm_eq : ‖d‖ = t := by
      rw [step, norm_smul, Real.norm_eq_abs, abs_of_pos positive, R.exterior.unit w, mul_one]
    rw [norm_eq, step, real_inner_smul_right]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right radial positive.le
  · have parent_eq : R.parents.parent v = R.original.parents.parent v :=
      R.original.parents.attach_parent_nonroot R.exterior.parents R.shared_height root
    have original := R.original.radial v root q history s time
    dsimp only [d]
    rw [parent_eq]
    exact (mul_le_mul_of_nonneg_right interior_margin (by positivity)).trans original

/-- Every original-vertex history along the complete adaptive forest has
the radial margin at its next nonterminal parent step. -/
theorem ancestor_next_radial_margin {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (interior_margin : γ ≤ margin) (exterior_margin : γ ≤ η)
    {source v : C.Vertex Set.univ} (ancestor : R.parents.Ancestor source v)
    (nonterminal : v ∉ R.parents.roots) {s : ℝ} (time : 0 ≤ s) :
    let x := K.projectedVertex v
    let d := K.projectedVertex (R.parents.parent v) - x
    γ * (‖x + s • d - K.projectedVertex source‖ * ‖d‖) ≤
      inner ℝ (x + s • d - K.projectedVertex source) d :=
  R.parent_radial_margin nonnegative small interior_margin exterior_margin nonterminal
    (R.ancestor_progress ancestor) time

end Unfoldings.ConvexRoof.CompatibleAdaptiveRouting
