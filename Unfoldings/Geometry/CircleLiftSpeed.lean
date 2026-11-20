module

public import Unfoldings.Geometry.RotatedLineContact
public import Unfoldings.Geometry.RightSlopeBound

/-! A derivative bound on the active links controls a continuous real circle lift. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Set
open scoped Topology

/-- A continuous real heading follows finitely many moving circle contacts.
Each contact branch comes with a closed eligibility set, allowing line
extensions to agree accidentally with the contact outside their actual links. -/
theorem circleLift_speed_bound {I : Type*} [Finite I]
    {a b K r : ℝ} (ab : a ≤ b) (radius : 0 < r)
    (heading : ℝ → ℝ) (continuous : ContinuousOn heading (Icc a b))
    (contact : ℝ → ℂ) (expression : ∀ x ∈ Icc a b, contact x = (r : ℂ) * polarRay (heading x))
    (branch : I → ℝ → ℂ) (branch_cont : ∀ i, ContinuousOn (branch i) (Icc a b))
    (eligible : I → Set ℝ) (branch_closed : ∀ i, IsClosed (eligible i))
    (chooses : ∀ x ∈ Icc a b, ∃ i, x ∈ eligible i ∧ contact x = branch i x)
    (rates : ∀ x ∈ Ico a b, ∀ i, x ∈ eligible i → contact x = branch i x →
      ∃ d ≤ K, HasDerivAt (fun y => Complex.arg (branch i y / branch i x)) d x) :
    heading b - heading a ≤ K * (b - a) := by
  apply sub_le_mul_of_eventually_right_slope ab continuous
  intro x hx L KL
  have x_in : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  have subset : Ioc x b ⊆ Icc a b := fun y hy => ⟨hx.1.trans hy.1.le, hy.2⟩
  have contact_cont : ContinuousOn contact (Icc a b) := by
    have ray : Continuous polarRay := by
      unfold polarRay
      exact continuous_subtype_val.comp Circle.exp.continuous
    exact (continuousOn_const.mul (ray.comp_continuousOn continuous)).congr expression
  have angle_lt : ∀ᶠ y in 𝓝[Ioc x b] x, heading y - heading x ∈ Ioo (-Real.pi) Real.pi := by
    have limit : ContinuousWithinAt (fun y => heading y - heading x) (Ioc x b) x :=
      ((continuous x x_in).sub continuousWithinAt_const).mono subset
    apply limit
    change Ioo (-Real.pi) Real.pi ∈ 𝓝 (heading x - heading x)
    rw [sub_self]
    exact Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
  have phase {y : ℝ} (hy : y ∈ Icc a b) (near : heading y - heading x ∈ Ioo (-Real.pi) Real.pi) :
      Complex.arg (contact y / contact x) = heading y - heading x := by
    rw [expression y hy, expression x x_in,
      mul_div_mul_left _ _ (show (r : ℂ) ≠ 0 by exact_mod_cast radius.ne'), polarRay_div]
    exact Circle.arg_exp near.1 near.2.le
  have within : 𝓝[Ioc x b] x ≤ 𝓝[≠] x :=
    nhdsWithin_mono _ fun y hy => hy.1.ne'
  have each (i : I) : ∀ᶠ y in 𝓝[Ioc x b] x,
      y ∈ eligible i → contact y = branch i y → slope heading x y < L := by
    by_cases eligible_x : x ∈ eligible i
    · by_cases active : contact x = branch i x
      · obtain ⟨d, d_le, derivative⟩ := rates x hx i eligible_x active
        let g (y : ℝ) := Complex.arg (branch i y / branch i x)
        have g_zero : g x = 0 := by simp [g]
        have slope_lt : ∀ᶠ y in 𝓝[Ioc x b] x, slope g x y < L :=
          (derivative.tendsto_slope.mono_left within) (Iio_mem_nhds (d_le.trans_lt KL))
        filter_upwards [slope_lt, angle_lt, self_mem_nhdsWithin]
          with y hy_slope hy_close hy _ hcontact
        have same : g y = heading y - heading x := by
          dsimp [g]
          rw [← hcontact, ← active]
          exact phase (subset hy) hy_close
        simpa only [slope_def_field, g_zero, same, sub_zero] using hy_slope
      · have difference := ((contact_cont x x_in).sub (branch_cont i x x_in)).mono subset
        have op : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
        have ev : ∀ᶠ y in 𝓝[Ioc x b] x, contact y - branch i y ≠ 0 :=
          difference (op.mem_nhds (sub_ne_zero.mpr active))
        exact ev.mono fun y hy _ eq => (hy (sub_eq_zero.mpr eq)).elim
    · have ev : ∀ᶠ y in 𝓝[Ioc x b] x, y ∉ eligible i :=
        mem_nhdsWithin_of_mem_nhds ((branch_closed i).isOpen_compl.mem_nhds eligible_x)
      exact ev.mono fun y hy hit _ => (hy hit).elim
  filter_upwards [eventually_all.mpr each, self_mem_nhdsWithin] with y branches hy
  obtain ⟨i, allowed, agrees⟩ := chooses y (subset hy)
  exact branches i allowed agrees

/-- A fixed-radius intersection with a rotating collection of actual
closed links satisfies the integrated `2 / m` angular speed bound. The
parameter domains can be bounded edge intervals or a half-line for a tail. -/
theorem circleLift_speed_bound_of_rotating_links {I : Type*} [Finite I]
    {a b r m : ℝ} (ab : a ≤ b) (radius : 0 < r) (m_pos : 0 < m)
    (h : ℂ) (hinge : ‖h‖ ≤ r) (start direction : I → ℂ)
    (nonzero : ∀ i, direction i ≠ 0) (domain : I → Set ℝ)
    (closed : ∀ i, IsClosed (domain i))
    (heading : ℝ → ℝ) (continuous : ContinuousOn heading (Icc a b))
    (contact : ℝ → ℂ) (expression : ∀ x ∈ Icc a b, contact x = (r : ℂ) * polarRay (heading x))
    (chooses : ∀ x ∈ Icc a b, ∃ i, ∃ s ∈ domain i,
      contact x = h + polarRay x * (start i + s • direction i))
    (margin : ∀ x ∈ Icc a b, ∀ i, ∀ s ∈ domain i,
      contact x = h + polarRay x * (start i + s • direction i) →
      m * (r * ‖polarRay x * direction i‖) ≤ inner ℝ (contact x) (polarRay x * direction i)) :
    heading b - heading a ≤ (2 / m) * (b - a) := by
  let branch (i : I) := rotatingLineCircleContact h (start i) (direction i) r
  let param (i : I) := rotatingLineCircleParameter h (start i) (direction i) r
  let eligible (i : I) := param i ⁻¹' domain i
  have into (x : ℝ) (x_in : x ∈ Icc a b) : ‖contact x‖ = r := by
    rw [expression x x_in, norm_mul, norm_polarRay, mul_one, Complex.norm_real,
      Real.norm_of_nonneg radius.le]
  apply circleLift_speed_bound ab radius heading continuous contact expression branch
    (fun i => (continuous_rotatingLineCircleContact h (start i) (direction i) r
      (nonzero i)).continuousOn) eligible
    (fun i => (closed i).preimage
      (continuous_rotatingLineCircleParameter h (start i) (direction i) r (nonzero i)))
  · intro x x_in
    obtain ⟨i, s, in_domain, point⟩ := chooses x x_in
    have direction_pos : 0 < ‖polarRay x * direction i‖ :=
      norm_pos_iff.mpr (mul_ne_zero (polarRay_ne_zero x) (nonzero i))
    have trans : 0 < inner ℝ (contact x) (polarRay x * direction i) :=
      (mul_pos m_pos (mul_pos radius direction_pos)).trans_le
        (margin x x_in i s in_domain point)
    have eq := rotatingLineCircleParameter_eq_of_contact point (into x x_in) trans
    change param i x = s at eq
    refine ⟨i, show param i x ∈ domain i from eq.symm ▸ in_domain, ?_⟩
    exact point.trans (by
      change _ = rotatingLineCircleContact h (start i) (direction i) r x
      rw [rotatingLineCircleContact_eq]
      change _ = h + polarRay x * (start i + param i x • direction i)
      rw [eq])
  · intro x x_in i in_domain equal
    have x' : x ∈ Icc a b := ⟨x_in.1, x_in.2.le⟩
    have point : contact x = h + polarRay x * (start i + param i x • direction i) :=
      equal.trans (rotatingLineCircleContact_eq _ _ _ _ _)
    have on_circle : ‖h + polarRay x * (start i + param i x • direction i)‖ = r :=
      (congrArg norm point).symm.trans (into x x')
    have rad := margin x x' i (param i x) in_domain point
    rw [point] at rad
    exact exists_rotatingLineCircleContact_angle_derivative_le radius m_pos (nonzero i) hinge
      on_circle rad

end Unfoldings
