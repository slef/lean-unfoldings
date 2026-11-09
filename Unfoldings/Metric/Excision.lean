module

public import Unfoldings.Metric.LocalSeams

/-!
# Local metric excision for finite closed seams

Cutting seams that do not meet a chosen equivalence class leaves a sufficiently
small whole intrinsic ball unchanged. The isometry is the canonical map that
restores those seams. No global development or manifold premise is required.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w z

variable {ι : Type u} (E : ι → Type v) [∀ i, MetricSpace (E i)]

/-- Restoring seams restricts to a canonical map between corresponding metric balls. -/
def forgetBall {R S : Total E → Total E → Prop} (inclusion : ∀ a b, R a b → S a b)
    (a : Total E) (r : ℝ≥0∞) : Metric.eball (point E R a) r → Metric.eball (point E S a) r :=
  fun x => ⟨forget E inclusion x.val, by
    have bound := (forget_lipschitz E inclusion).edist_le_mul x.val (point E R a)
    simp only [ENNReal.coe_one, one_mul, forget_point] at bound
    exact bound.trans_lt x.property⟩

theorem forgetBall_isometry {R S : Total E → Total E → Prop}
    (inclusion : ∀ a b, R a b → S a b) (a : Total E) (r : ℝ≥0∞)
    (lower : ∀ b c, edist (point E S a) (point E S b) < r →
      edist (point E S a) (point E S c) < r →
      edist (point E R b) (point E R c) ≤ edist (point E S b) (point E S c)) :
    Isometry (forgetBall E inclusion a r) := by
  have upper (b c : Total E) : edist (point E S b) (point E S c) ≤
      edist (point E R b) (point E R c) := distance_antitone E inclusion b c
  intro x y
  obtain ⟨b, hb⟩ := point_surjective E R x.val
  obtain ⟨c, hc⟩ := point_surjective E R y.val
  have near_b : edist (point E S a) (point E S b) < r := by
    apply (upper a b).trans_lt
    rw [hb, edist_comm]
    exact x.property
  have near_c : edist (point E S a) (point E S c) < r := by
    apply (upper a c).trans_lt
    rw [hc, edist_comm]
    exact y.property
  change edist (forget E inclusion x.val) (forget E inclusion y.val) = edist x.val y.val
  rw [← hb, ← hc, forget_point, forget_point]
  exact le_antisymm (upper b c) (lower b c near_b near_c)

theorem forgetBall_surjective {R S : Total E → Total E → Prop}
    (inclusion : ∀ a b, R a b → S a b) (a : Total E) {r : ℝ≥0∞} (positive : 0 < r)
    (lower : ∀ b c, edist (point E S a) (point E S b) < r →
      edist (point E S a) (point E S c) < r →
      edist (point E R b) (point E R c) ≤ edist (point E S b) (point E S c)) :
    Function.Surjective (forgetBall E inclusion a r) := by
  intro y
  obtain ⟨b, hb⟩ := point_surjective E S y.val
  have near : edist (point E S a) (point E S b) < r := by
    rw [hb, edist_comm]
    exact y.property
  have center_near : edist (point E S a) (point E S a) < r := by
    simpa only [edist_self] using positive
  have lifted : edist (point E R a) (point E R b) < r :=
    (lower a b center_near near).trans_lt near
  let x : Metric.eball (point E R a) r := ⟨point E R b, by
    rw [Metric.mem_eball, edist_comm]
    exact lifted⟩
  exact ⟨x, Subtype.ext ((forget_point E inclusion b).trans hb)⟩

/-- Local distance lower bounds give a whole-ball isometry using the canonical seam map. -/
def forgetBallIsometry {R S : Total E → Total E → Prop}
    (inclusion : ∀ a b, R a b → S a b) (a : Total E) {r : ℝ≥0∞} (positive : 0 < r)
    (lower : ∀ b c, edist (point E S a) (point E S b) < r →
      edist (point E S a) (point E S c) < r →
      edist (point E R b) (point E R c) ≤ edist (point E S b) (point E S c)) :
    Metric.eball (point E R a) r ≃ᵢ Metric.eball (point E S a) r :=
  ⟨Equiv.ofBijective (forgetBall E inclusion a r)
    ⟨(forgetBall_isometry E inclusion a r lower).injective,
      forgetBall_surjective E inclusion a positive lower⟩,
    forgetBall_isometry E inclusion a r lower⟩

@[simp] theorem forgetBallIsometry_apply {R S : Total E → Total E → Prop}
    (inclusion : ∀ a b, R a b → S a b) (a : Total E) {r : ℝ≥0∞} (positive : 0 < r)
    (lower : ∀ b c, edist (point E S a) (point E S b) < r →
      edist (point E S a) (point E S c) < r →
      edist (point E R b) (point E R c) ≤ edist (point E S b) (point E S c))
    (x : Metric.eball (point E R a) r) :
    (forgetBallIsometry E inclusion a positive lower x).val = forget E inclusion x.val := rfl

/-- A constructed whole-ball comparison under restoration of seams. -/
structure ForgetChart {R S : Total E → Total E → Prop}
    (inclusion : ∀ a b, R a b → S a b) (a : Total E) where
  radius : ℝ
  positive : 0 < radius
  chart : Metric.eball (point E R a) (ENNReal.ofReal radius) ≃ᵢ
    Metric.eball (point E S a) (ENNReal.ofReal radius)
  agrees : ∀ x, (chart x).val = forget E inclusion x.val

namespace ClosedSeams

variable {E} (S : ClosedSeams.{u, v, w, z} E)

/-- Keep the incident seams and cut any others: a small whole ball retains its metric. -/
theorem exists_forgetChart (a : Total E) (finite : ∀ i, (classIn E S.relation a i).Finite)
    (R : Total E → Total E → Prop) (inclusion : ∀ x y, R x y → S.relation x y)
    (kept : ∀ s, S.Incident a s → ∀ x, R ⟨S.left s, S.toLeft s x⟩
      ⟨S.right s, S.toRight s x⟩) : Nonempty (ForgetChart E inclusion a) := by
  have compatible : ∀ s, S.Incident a s → ∀ x,
      of E R (S.left s) (S.toLeft s x) = of E R (S.right s) (S.toRight s x) := by
    intro s incident x
    exact point_eq_of_glue E (kept s incident x)
  obtain ⟨r, positive, lower⟩ := S.exists_radius_map_edist_le a finite (of E R)
    (of_lipschitz E R) compatible
  exact ⟨⟨r, positive, forgetBallIsometry E inclusion a (ENNReal.ofReal_pos.mpr positive) lower,
    fun _ => rfl⟩⟩

end ClosedSeams
end Unfoldings.MetricGluing
