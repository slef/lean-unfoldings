module

public import Unfoldings.Geometry.SpatialEnvelopeCutBanks
public import Unfoldings.Geometry.AffineEnvelopeActiveGerm
public import Unfoldings.Geometry.AffineLineSide

/-! A straight ray in a finite supported roof has fixed rigid one-sided neighborhoods. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {p q : Plane}

private theorem lineMap_endpoints_zero {a b t : ℝ} (positive : 0 < t)
    (nonnegative : ∀ s : ℝ, 0 ≤ s → 0 ≤ AffineMap.lineMap a b s)
    (zero : AffineMap.lineMap a b t = 0) : a = 0 ∧ b = 0 := by
  have source := nonnegative 0 le_rfl
  rw [AffineMap.lineMap_apply_zero] at source
  have later := nonnegative (2 * t) (by positivity)
  rw [AffineMap.lineMap_apply_ring'] at zero later
  have a_zero : a = 0 := by linarith only [source, zero, later]
  rw [a_zero, sub_zero, add_zero] at zero
  exact ⟨a_zero, (mul_eq_zero.mp zero).resolve_left positive.ne'⟩

/-- An actual plane active anywhere on the open straight ray is active also
at its source and everywhere on its continuation. -/
theorem support_eq_on_straight_ray
    (linear : ∀ t : ℝ, 0 ≤ t → height family (AffineMap.lineMap p q t) =
      AffineMap.lineMap (height family p) (height family q) t)
    (i : I) {t : ℝ} (positive : 0 < t)
    (active : height family (AffineMap.lineMap p q t) = (family i).height (AffineMap.lineMap p q t)) :
    ∀ s : ℝ, 0 ≤ s → height family (AffineMap.lineMap p q s) =
      (family i).height (AffineMap.lineMap p q s) := by
  let a := (family i).height p - height family p
  let b := (family i).height q - height family q
  have gap (s : ℝ) (nonnegative : 0 ≤ s) :
      AffineMap.lineMap a b s =
        (family i).height (AffineMap.lineMap p q s) - height family (AffineMap.lineMap p q s) := by
    rw [(family i).height.apply_lineMap, linear s nonnegative]
    simp only [AffineMap.lineMap_apply_ring, a, b]
    ring
  obtain ⟨az, bz⟩ := lineMap_endpoints_zero positive
    (fun s hs => by
      rw [gap s hs]
      exact sub_nonneg.mpr (AffineEnvelope.height_le _ _ i))
    (by rw [gap t positive.le, active, sub_self])
  intro s hs
  have equal := gap s hs
  rw [az, bz, AffineMap.lineMap_same_apply] at equal
  exact (sub_eq_zero.mp equal.symm).symm

namespace WholePartition

variable {A : Type u} [Finite A] (P : WholePartition family A)
  (genuine : p ≠ q) (signs : A → Bool)
  (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed (orientMap p q) (signs a) x)
  (linear : ∀ t : ℝ, 0 ≤ t → height family (AffineMap.lineMap p q t) =
    AffineMap.lineMap (height family p) (height family q) t)

omit [Finite A] in
include genuine aligned linear in
private theorem support_le_on_ray_side (a : A) {t : ℝ} (positive : 0 < t)
    (active_a : height family (AffineMap.lineMap p q t) =
      (family (P.support a)).height (AffineMap.lineMap p q t))
    (i : I) (active_i : height family (AffineMap.lineMap p q t) =
      (family i).height (AffineMap.lineMap p q t))
    {z : Plane} (side : 0 ≤ AffineArrangement.signed (orientMap p q) (signs a) z) :
    (family (P.support a)).height z ≤ (family i).height z := by
  obtain ⟨c, inside⟩ := P.full a
  have member := interior_subset inside
  have nonzero : AffineArrangement.signed (orientMap p q) (signs a) ≠ 0 := by
    have proper := orientMap_ne_zero genuine
    cases value : signs a <;>
      simpa only [value, AffineArrangement.signed, Bool.false_eq_true, ↓reduceIte, neg_ne_zero]
        using proper
  have strict : 0 < AffineArrangement.signed (orientMap p q) (signs a) c := by
    apply lt_of_le_of_ne (aligned a c member)
    intro zero
    exact not_mem_interior_of_affine_lower_bound _ nonzero (aligned a) zero.symm inside
  have on_ray (s : ℝ) (nonnegative : 0 ≤ s) :
      ((family i).height - (family (P.support a)).height) (AffineMap.lineMap p q s) = 0 := by
    change (family i).height _ - (family (P.support a)).height _ = 0
    rw [← support_eq_on_straight_ray linear i positive active_i s nonnegative,
      ← support_eq_on_straight_ray linear (P.support a) positive active_a s nonnegative, sub_self]
  have at_p := on_ray 0 le_rfl
  have at_q := on_ray 1 zero_le_one
  rw [AffineMap.lineMap_apply_zero] at at_p
  rw [AffineMap.lineMap_apply_one] at at_q
  have test : 0 ≤ ((family i).height - (family (P.support a)).height) c := by
    change 0 ≤ (family i).height c - (family (P.support a)).height c
    apply sub_nonneg.mpr
    rw [← P.active a c member]
    exact AffineEnvelope.height_le _ _ i
  have nonnegative := affine_nonnegative_on_signed_side
    ((family i).height - (family (P.support a)).height) p q c at_p at_q test (signs a)
    (by simpa only [AffineArrangement.signed_apply, orientMap_apply] using strict)
    (by simpa only [AffineArrangement.signed_apply, orientMap_apply] using side)
  exact sub_nonneg.mp nonnegative

include genuine aligned linear in
/-- Two fixed cells supply the actual supporting plane of each closed halfplane
germ at every positive point of the straight ray. -/
theorem exists_straightRay_support_cells :
    ∃ (anchor : Bool → A) (T : ℝ), 0 < T ∧ (∀ side, signs (anchor side) = side) ∧
      (∀ side t, T ≤ t → AffineMap.lineMap p q t ∈ P.footprint (anchor side)) ∧
      (∀ side (t : ℝ), 0 ≤ t → height family (AffineMap.lineMap p q t) =
        (family (P.support (anchor side))).height (AffineMap.lineMap p q t)) ∧
      ∀ side (t : ℝ), 0 < t → ∃ r > 0, ∀ z, dist z (AffineMap.lineMap p q t) < r →
        0 ≤ AffineArrangement.signed (orientMap p q) side z →
        height family z = (family (P.support (anchor side))).height z := by
  obtain ⟨l, r, left, right, T, T_pos, tail⟩ := P.exists_opposite_ray_cells
    (orientMap p q) (orientMap_ne_zero genuine) signs aligned p (q - p) (fun t => by
      rw [add_comm, ← AffineMap.lineMap_apply_module', orientMap_apply, orient_lineMap])
  let anchor (side : Bool) := if side then l else r
  have sign_eq (side : Bool) : signs (anchor side) = side := by
    cases side
    · exact right
    · exact left
  have final (side : Bool) (t : ℝ) (after : T ≤ t) :
      AffineMap.lineMap p q t ∈ P.footprint (anchor side) := by
    rw [AffineMap.lineMap_apply_module', add_comm]
    cases side
    · exact (tail t after).2
    · exact (tail t after).1
  have active (side : Bool) (t : ℝ) (nonnegative : 0 ≤ t) :
      height family (AffineMap.lineMap p q t) =
        (family (P.support (anchor side))).height (AffineMap.lineMap p q t) :=
    support_eq_on_straight_ray linear (P.support (anchor side)) T_pos
      (P.active (anchor side) _ (final side T le_rfl)) t nonnegative
  refine ⟨anchor, T, T_pos, sign_eq, final, active, ?_⟩
  intro side t positive
  apply AffineEnvelope.exists_radius_height_eq_on_region (fun i => (family i).height)
    (P.support (anchor side)) (AffineMap.lineMap p q t) (active side t positive.le)
    {z | 0 ≤ AffineArrangement.signed (orientMap p q) side z}
  intro i current z on_side
  exact P.support_le_on_ray_side genuine signs aligned linear (anchor side) positive
    (active side t positive.le) i current (by rwa [sign_eq])

end WholePartition
end Unfoldings.SpatialEnvelope
