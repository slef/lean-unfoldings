module

public import Unfoldings.FewestNets.SingleCellEuler
public import Unfoldings.FewestNets.SingleCellReflections
public import Unfoldings.Geometry.SpatialRotationSphere

/-! Average the pointwise Euler expression using equal spherical site marginals. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SingleCellCharge

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- A binary membership with a measurable selected set is integrable. -/
theorem integrable_membershipValue (inside : Ω → Bool)
    (measurable : MeasurableSet {x | inside x = true}) :
    Integrable (fun x => membershipValue (inside x)) μ := by
  let s := {x | inside x = true}
  have indicator : (fun x => membershipValue (inside x)) = s.indicator (fun _ => 1) := by
    funext x
    cases hx : inside x <;> simp [membershipValue, s, hx]
  rw [indicator]
  exact (integrable_indicator_iff measurable).2 (integrable_const (1 : ℝ)).integrableOn

/-- On any finite measure space with a common site marginal, the linear
part of the Euler expression averages to the Euler number times that marginal. -/
theorem integral_binary_euler_of_equal_marginals [DecidableEq E]
    (left right : E → V) (sides : F → Finset E) (marked₀ marked₁ : F → E)
    (twice : ∀ e, (Finset.univ.filter fun f => e ∈ sides f).card = 2)
    (inside : Ω → V → Bool) (full : Ω → F → Bool) (mass : ℝ)
    (measurable : ∀ v, MeasurableSet {x | inside x v = true})
    (equal : ∀ v, ∫ x, membershipValue (inside x v) ∂μ = mass) :
    let edge (x : Ω) (e : E) := (inside x (left e), inside x (right e))
    let signed (x : Ω) (f : F) := charge (∑ e ∈ sides f, crossing (edge x e))
      (edge x (marked₀ f)) (edge x (marked₁ f)) (full x f)
    (∀ f, Integrable (fun x => signed x f) μ) →
    (∫ x, ((∑ v, membershipValue (inside x v)) -
      (∑ e, membershipValue (inside x (left e) && inside x (right e))) +
      (∑ f, membershipValue (full x f))) ∂μ) =
      ((Fintype.card V : ℝ) - Fintype.card E + Fintype.card F) * mass +
        ∑ f, ∫ x, signed x f ∂μ := by
  classical
  dsimp only
  intro charge_integrable
  let flag (v : V) (x : Ω) := membershipValue (inside x v)
  let ends (e : E) (x : Ω) := endpoints (inside x (left e), inside x (right e))
  let sites (x : Ω) := ∑ v, flag v x
  let edges (x : Ω) := ∑ e, ends e x
  let marks (x : Ω) := ∑ f, (ends (marked₀ f) x + ends (marked₁ f) x)
  let costs (x : Ω) (f : F) :=
    charge (∑ e ∈ sides f, crossing (inside x (left e), inside x (right e)))
      (inside x (left (marked₀ f)), inside x (right (marked₀ f)))
      (inside x (left (marked₁ f)), inside x (right (marked₁ f))) (full x f)
  let charges (x : Ω) := ∑ f, costs x f
  have flag_int (v : V) : Integrable (flag v) μ :=
    integrable_membershipValue (fun x => inside x v) (measurable v)
  have ends_int (e : E) : Integrable (ends e) μ :=
    (flag_int (left e)).add (flag_int (right e))
  have marks_int (f : F) :
      Integrable (fun x => ends (marked₀ f) x + ends (marked₁ f) x) μ :=
    (ends_int (marked₀ f)).add (ends_int (marked₁ f))
  have sites_int : Integrable sites μ := integrable_finsetSum _ (fun v _ => flag_int v)
  have edges_int : Integrable edges μ := integrable_finsetSum _ (fun e _ => ends_int e)
  have all_marks_int : Integrable marks μ := integrable_finsetSum _ (fun f _ => marks_int f)
  have charges_int : Integrable charges μ :=
    integrable_finsetSum _ (fun f _ => charge_integrable f)
  have ends_mass (e : E) : (∫ x, ends e x ∂μ) = 2 * mass := by
    change (∫ x, (flag (left e) x + flag (right e) x) ∂μ) = 2 * mass
    rw [integral_add (flag_int _) (flag_int _), equal (left e), equal (right e)]
    ring
  have sites_mass : (∫ x, sites x ∂μ) = Fintype.card V * mass := by
    dsimp only [sites, flag]
    rw [integral_finsetSum _ (fun v _ => flag_int v)]
    simp only [flag, equal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have edges_mass : (∫ x, edges x ∂μ) = Fintype.card E * (2 * mass) := by
    dsimp only [edges]
    rw [integral_finsetSum _ (fun e _ => ends_int e)]
    simp only [ends_mass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have marks_mass : (∫ x, marks x ∂μ) = Fintype.card F * (4 * mass) := by
    dsimp only [marks]
    rw [integral_finsetSum _ (fun f _ => marks_int f)]
    simp only [integral_add (ends_int _) (ends_int _), ends_mass]
    rw [show 2 * mass + 2 * mass = 4 * mass by ring]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have pointwise (x : Ω) : ((∑ v, membershipValue (inside x v)) -
      (∑ e, membershipValue (inside x (left e) && inside x (right e))) +
      (∑ f, membershipValue (full x f))) =
        sites x - edges x / 2 + marks x / 4 + charges x :=
    binary_euler_linearization left right sides marked₀ marked₁ twice (inside x) (full x)
  simp_rw [pointwise]
  have half_int : Integrable (fun x => edges x / 2) μ := edges_int.div_const _
  have quarter_int : Integrable (fun x => marks x / 4) μ := all_marks_int.div_const _
  have plus_charges := integral_add
    (f := fun x => sites x - edges x / 2 + marks x / 4) ((sites_int.sub half_int).add quarter_int)
    charges_int
  have plus_marks := integral_add (f := fun x => sites x - edges x / 2)
    (sites_int.sub half_int) quarter_int
  have minus_edges := integral_sub (g := fun x => edges x / 2) sites_int half_int
  rw [plus_charges, plus_marks, minus_edges,
    integral_div, integral_div, sites_mass, edges_mass, marks_mass]
  dsimp only [charges]
  rw [integral_finsetSum _ (fun f _ => charge_integrable f)]
  ring

end Unfoldings.FewestNets.SingleCellCharge
