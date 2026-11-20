module

public import Unfoldings.Geometry.CircleLiftSpeed
public import Unfoldings.Geometry.HingeCircleLift

/-! The actual hinge-circle lift satisfies the integrated angular speed bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

open scoped NNReal Topology

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (positive : 0 < angle) (outward : (R.suffix hinge).Outward) (small : angle < Real.pi)

include outward small in
/-- The actual circle contact rotates by at most twice the opening angle
divided by its common radial margin. The tests concern all points on each
moved closed edge or tail, including both sides of changes of active link. -/
theorem hingeCircleLift_last_le_of_margin
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) {m : ℝ} (m_pos : 0 < m)
    (edges_ne : ∀ i, (R.suffix hinge).chain.edge i ≠ 0)
    (edge_margin : ∀ θ ∈ Set.Icc 0 angle, ∀ i (t : unitInterval),
      let p := R.chain.vertex hinge - R.start +
        polarRay θ * ((R.suffix hinge).chain.point i t - (R.suffix hinge).start)
      let d := polarRay θ * (R.suffix hinge).chain.edge i
      m * (‖p‖ * ‖d‖) ≤ inner ℝ p d)
    (tail_margin : ∀ θ ∈ Set.Icc 0 angle, ∀ t : ℝ≥0,
      let p := R.chain.vertex hinge - R.start +
        polarRay θ * ((R.suffix hinge).tail t - (R.suffix hinge).start)
      let d := polarRay θ * (R.suffix hinge).direction
      m * (‖p‖ * ‖d‖) ≤ inner ℝ p d) :
    R.hingeCircleLift hinge nonzero angle radial positive r ⟨angle, positive.le, le_rfl⟩ ≤
      (2 / m) * angle := by
  classical
  let o : Set.Icc (0 : ℝ) angle := ⟨0, le_rfl, positive.le⟩
  let toInterval (t : ℝ) : Set.Icc 0 angle := if h : t ∈ Set.Icc 0 angle then ⟨t, h⟩ else o
  have in_interval {t : ℝ} (ht : t ∈ Set.Icc 0 angle) : toInterval t = ⟨t, ht⟩ := by
    simp only [toInterval, dite_eq_left ht]
  let S := R.suffix hinge
  let h := R.chain.vertex hinge - R.start
  let start : Fin (n - hinge.val) ⊕ Unit → ℂ
    | .inl i => S.chain.vertex i.castSucc - S.start
    | .inr _ => S.chain.vertex (Fin.last (n - hinge.val)) - S.start
  let direction : Fin (n - hinge.val) ⊕ Unit → ℂ
    | .inl i => S.chain.edge i
    | .inr _ => S.direction
  let domain : Fin (n - hinge.val) ⊕ Unit → Set ℝ
    | .inl _ => Set.Icc 0 1
    | .inr _ => Set.Ici 0
  have dir_ne (i) : direction i ≠ 0 := by
    cases i with
    | inl j => exact edges_ne j
    | inr j => exact nonzero
  have domain_closed (i) : IsClosed (domain i) := by
    cases i with
    | inl j => exact isClosed_Icc
    | inr j => exact isClosed_Ici
  have hinge_radius : ‖h‖ < ((r.val : ℝ≥0) : ℝ) :=
    by
      have above : dist R.start (R.chain.vertex hinge) < (r.val : ℝ) := r.property
      simpa only [h, dist_eq_norm'] using above
  have r_pos : 0 < (r.val : ℝ) := (norm_nonneg h).trans_lt hinge_radius
  let initial := R.hingeExteriorDirection hinge nonzero angle radial (o, r)
  let lift (t : Set.Icc (0 : ℝ) angle) := R.hingeCircleLift hinge nonzero angle radial positive r t
  let heading (t : ℝ) := lift (toInterval t) + (initial : ℂ).arg
  let contact (t : ℝ) :=
    R.hingeCirclePoint hinge nonzero angle radial r.val (toInterval t) - R.start
  have continuous : ContinuousOn heading (Set.Icc 0 angle) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have restrict_eq : (Set.Icc 0 angle).domRestrict heading =
        fun t : Set.Icc (0 : ℝ) angle => lift t + (initial : ℂ).arg := by
      funext t
      change lift (toInterval t.val) + _ = _
      rw [in_interval t.property]
    rw [restrict_eq]
    exact (R.continuous_hingeCircleLift hinge nonzero angle radial positive outward small r).add
      continuous_const
  have expression (t : ℝ) (ht : t ∈ Set.Icc 0 angle) :
      contact t = ((r.val : ℝ) : ℂ) * polarRay (heading t) := by
    have lift_phases : Circle.exp (heading t) =
        R.hingeExteriorDirection hinge nonzero angle radial (toInterval t, r) := by
      rw [show heading t = lift (toInterval t) + (initial : ℂ).arg from rfl, Circle.exp_add]
      change Circle.exp (R.hingeCircleLift hinge nonzero angle radial positive r (toInterval t)) *
        Circle.exp ((initial : ℂ).arg) = _
      rw [R.exp_hingeCircleLift, Circle.exp_arg]
      exact div_mul_cancel _ _
    have val := congrArg (fun p : Circle => (p : ℂ)) lift_phases
    rw [R.hingeExteriorDirection_coe] at val
    have rad_ne : ((r.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast r_pos.ne'
    change polarRay (heading t) = contact t / ((r.val : ℝ) : ℂ) at val
    rw [val, mul_div_cancel₀ _ rad_ne]
  have point_eq (i : Fin (n - hinge.val)) (t : unitInterval) :
      S.chain.point i t - S.start = start (.inl i) + (t : ℝ) • direction (.inl i) := by
    rw [PolygonalChain.point, AffineMap.lineMap_apply_module']
    change (t : ℝ) • S.chain.edge i + S.chain.vertex i.castSucc - S.start =
      (S.chain.vertex i.castSucc - S.start) + (t : ℝ) • S.chain.edge i
    abel
  have tail_eq (t : ℝ≥0) :
      S.tail t - S.start = start (.inr ()) + (t : ℝ) • direction (.inr ()) := by
    change (S.chain.vertex (Fin.last _) + (t : ℝ) • S.direction) - S.start =
      (S.chain.vertex (Fin.last _) - S.start) + (t : ℝ) • S.direction
    abel
  have chooses (t : ℝ) (ht : t ∈ Set.Icc 0 angle) :
      ∃ i, ∃ s ∈ domain i, contact t = h + polarRay t * (start i + s • direction i) := by
    obtain ⟨x, hx, image⟩ := R.hingeCirclePoint_mem_suffix hinge nonzero angle radial
      r.val r.property (toInterval t)
    have move : contact t = h + polarRay t * (x - S.start) := by
      change S.start + complexRotation (toInterval t).val (x - S.start) =
        R.hingeCirclePoint hinge nonzero angle radial r.val (toInterval t) at image
      change R.hingeCirclePoint hinge nonzero angle radial r.val (toInterval t) - R.start = _
      rw [← image, complexRotation_apply, in_interval ht]
      have start_at_hinge : S.start = R.chain.vertex hinge := R.suffix_start hinge
      rw [start_at_hinge]
      dsimp only [h]
      abel
    rcases hx with hx | hx
    · rw [S.chain.path_range] at hx
      rcases hx with start_hit | interiors
      · have eq : x = S.start := start_hit
        rw [eq, sub_self, mul_zero, add_zero] at move
        have radius := R.hingeCirclePoint_radius hinge nonzero angle radial r.val (toInterval t)
        rw [dist_eq_norm'] at radius
        change ‖contact t‖ = _ at radius
        exact False.elim ((ne_of_lt hinge_radius) (move ▸ radius))
      · obtain ⟨i, t', rfl⟩ := Set.mem_iUnion.mp interiors
        exact ⟨.inl i, t'.val, t'.property, move.trans (by rw [point_eq])⟩
    · obtain ⟨t', rfl⟩ := hx
      exact ⟨.inr (), (t' : ℝ), t'.coe_nonneg, move.trans (by rw [tail_eq])⟩
  have bound := circleLift_speed_bound_of_rotating_links positive.le r_pos m_pos h
    hinge_radius.le start direction dir_ne domain domain_closed heading continuous contact
    expression chooses (fun t ht i s allowed equal => by
      have norm_at : ‖contact t‖ = (r.val : ℝ) := by
        rw [expression t ht, norm_mul, norm_polarRay, mul_one, Complex.norm_real,
          Real.norm_of_nonneg r_pos.le]
      rw [← norm_at, equal]
      cases i with
      | inl i =>
        let p : unitInterval := ⟨s, allowed⟩
        have exact_margin := edge_margin t ht i p
        rw [point_eq i p] at exact_margin
        exact exact_margin
      | inr t' =>
        let p : ℝ≥0 := ⟨s, allowed⟩
        have exact_margin := tail_margin t ht p
        rw [tail_eq p] at exact_margin
        exact exact_margin)
  simp only [heading, in_interval (show angle ∈ Set.Icc 0 angle from ⟨positive.le, le_rfl⟩),
    in_interval (show 0 ∈ Set.Icc 0 angle from ⟨le_rfl, positive.le⟩), lift,
    R.hingeCircleLift_zero, sub_zero, zero_add, add_sub_cancel_right] at bound
  exact bound

end Unfoldings.PolygonalRay
