module

public import Unfoldings.Cap.SharpSectionFans
public import Unfoldings.Topology.ChainSplit

/-! A regular straight fan has the sharp intrinsic bend bound on the actual link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

private theorem slope_eq_initial_final_of_unique_change {n : ℕ} (f : Fin (n + 1) → Plane)
    (i : Fin n) (unchanged : ∀ j : Fin n, j ≠ i → f j.castSucc = f j.succ) :
    (∀ j : Fin (n + 1), j.val ≤ i.val → f j = f 0) ∧
      (∀ j : Fin (n + 1), i.val < j.val → f j = f (Fin.last n)) := by
  constructor
  · intro j
    refine Fin.induction (fun _ => rfl) (fun k prev hk => ?_) j
    have earlier : k.val < i.val := by
      change k.val + 1 ≤ i.val at hk
      omega
    exact (unchanged k (ne_of_lt earlier)).symm.trans (prev earlier.le)
  · have suffix (j : Fin (n + 1)) : i.val < j.val → f j = f i.succ := by
      refine Fin.induction (fun h => (Nat.not_lt_zero _ h).elim) (fun k prev hk => ?_) j
      by_cases same : k = i
      · rw [same]
      · have later : i.val < k.val := by
          have vals : k.val ≠ i.val := fun h => same (Fin.ext h)
          simp only [Fin.val_succ] at hk
          omega
        exact (unchanged k same).symm.trans (prev later)
    intro j hj
    exact (suffix j hj).trans (suffix (Fin.last n) i.isLt).symm

/-- If the real selected fan has only one or two slopes, a transverse straight
contact is either flat or has one genuine crease, even after subdivision. -/
theorem abs_straight_link_turn_le_sin_tilt {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    {w : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ w).Chain n)
    (d a b : Plane)
    (slopes : ∀ i, K.normalSlope (c.point i).val.1.1 = a ∨
      K.normalSlope (c.point i).val.1.1 = b)
    (transverse : a = b ∨ inner ℝ (a - b) d ≠ 0)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (first : K.projectedIntervalRay c 0 = t • d)
    (last : K.projectedIntervalRay c (Fin.last (n + 1)) = u • (-d))
    (projected : (∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) = π) :
    |π - ∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2| ≤
      sin φ * angle (K.spatialDirection c.first.val.1.1 d) (K.spatialDirection c.last.val.1.1 d) := by
  let f (i : Fin (n + 1)) := K.normalSlope (c.point i).val.1.1
  let l := c.first.val.1.1
  let r := c.last.val.1.1
  let intrinsic (p : C.LinkGerm Set.univ w) := (C.triangle p.val.1.1).cornerAngle p.val.1.2
  let planar (p : C.LinkGerm Set.univ w) := (K.projectedTriangle p.val.1.1).cornerAngle p.val.1.2
  have scale (f₀ : Face) (s : ℝ) (x : Plane) :
      K.spatialDirection f₀ (s • x) = s • K.spatialDirection f₀ x := by
    simp only [spatialDirection, pullbackDirection, map_smul]
  have neg (f₀ : Face) (x : Plane) : K.spatialDirection f₀ (-x) = -K.spatialDirection f₀ x := by
    simp only [spatialDirection, pullbackDirection, map_neg]
  have genuine : d ≠ 0 := by
    intro zero
    exact K.projectedIntervalRay_ne_zero c 0 (by rw [first, zero, smul_zero])
  by_cases changed : ∃ i : Fin n, f i.castSucc ≠ f i.succ
  · obtain ⟨i, switch⟩ := changed
    have across : inner ℝ (a - b) d ≠ 0 := by
      rcases transverse with same | valid
      · have all (j : Fin (n + 1)) : f j = b :=
          (slopes j).elim (fun eq => eq.trans same) id
        exact (switch ((all _).trans (all _).symm)).elim
      · exact valid
    have no_other (j : Fin n) (diff : j ≠ i) : f j.castSucc = f j.succ := by
      by_contra bad
      apply diff
      exact K.slope_change_index_unique c slopes (by
        rw [first, real_inner_smul_right]
        exact mul_ne_zero ht.ne' across) projected.le bad switch
    obtain ⟨prefix_slope, suffix_slope⟩ := slope_eq_initial_final_of_unique_change f i no_other
    let L := c.initial i.val i.isLt.le
    let R := c.suffix (i.val + 1) i.isLt
    have left_slopes (k : Fin (i.val + 1)) :
        K.normalSlope (L.point k).val.1.1 = K.normalSlope l := by
      let j : Fin (n + 1) := ⟨k.val, by have h := k.isLt; omega⟩
      exact prefix_slope j (by change k.val ≤ i.val; have h := k.isLt; omega)
    have right_slopes (k : Fin (n - (i.val + 1) + 1)) :
        K.normalSlope (R.point k).val.1.1 = K.normalSlope r := by
      let j : Fin (n + 1) := ⟨i.val + 1 + k.val, by
        have h := k.isLt
        have hi := i.isLt
        omega⟩
      exact suffix_slope j (by change i.val < i.val + 1 + k.val; omega)
    have sum_proj := c.sum_initial_suffix i planar
    rw [projected] at sum_proj
    have L_short : (∑ k, planar (L.point k)) ≤ π := by
      have rn : 0 ≤ ∑ k, planar (R.point k) :=
        Finset.sum_nonneg (fun _ _ => angle_nonneg _ _)
      linarith only [sum_proj, rn]
    have R_short : (∑ k, planar (R.point k)) ≤ π := by
      have ln : 0 ≤ ∑ k, planar (L.point k) :=
        Finset.sum_nonneg (fun _ _ => angle_nonneg _ _)
      linarith only [sum_proj, ln]
    have left_angles := K.sum_flat_link_corner_angles L l left_slopes
      (K.projectedInterval_halfplane_of_sum_le_pi L L_short)
    have right_angles := K.sum_flat_link_corner_angles R r right_slopes
      (K.projectedInterval_halfplane_of_sum_le_pi R R_short)
    let join := K.projectedIntervalRay c i.castSucc.succ
    have ray_zero {k : ℕ} (chain : (C.linkSystem Set.univ w).Chain k) :
        K.projectedIntervalRay chain 0 = K.projectedGermRay chain.first :=
      K.projectedIntervalRay_castSucc chain 0
    have L_first : K.projectedIntervalRay L 0 = t • d := by
      dsimp only [L]
      rw [ray_zero, c.initial_first, ← ray_zero]
      exact first
    have L_last : K.projectedIntervalRay L (Fin.last (i.val + 1)) = join := by
      dsimp only [L, join]
      rw [K.projectedIntervalRay_last, c.initial_last, K.projectedIntervalRay_succ] <;> rfl
    have R_first : K.projectedIntervalRay R 0 = join := by
      dsimp only [R, join]
      rw [ray_zero, c.suffix_first, Fin.succ_castSucc, K.projectedIntervalRay_castSucc] <;> rfl
    have R_last : K.projectedIntervalRay R (Fin.last (n - (i.val + 1) + 1)) = u • (-d) := by
      dsimp only [R]
      rw [K.projectedIntervalRay_last, c.suffix_last, ← K.projectedIntervalRay_last]
      exact last
    have lf : f i.castSucc = K.normalSlope l := prefix_slope i.castSucc le_rfl
    have rf : f i.succ = K.normalSlope r := suffix_slope i.succ (by simp)
    have tie : inner ℝ (K.normalSlope l - K.normalSlope r) join = 0 := by
      have e := K.projectedIntervalRay_normalSlope_tie c i
      change inner ℝ (f i.castSucc - f i.succ) join = 0 at e
      rwa [lf, rf] at e
    have opposite : (K.normalSlope l = a ∧ K.normalSlope r = b) ∨
        (K.normalSlope l = b ∧ K.normalSlope r = a) := by
      rcases slopes i.castSucc with la | lb <;> rcases slopes i.succ with ra | rb
      · exact (switch (la.trans ra.symm)).elim
      · exact Or.inl ⟨lf.symm.trans la, rf.symm.trans rb⟩
      · exact Or.inr ⟨lf.symm.trans lb, rf.symm.trans ra⟩
      · exact (switch (lb.trans rb.symm)).elim
    have d_diff : inner ℝ (K.normalSlope l - K.normalSlope r) d ≠ 0 := by
      rcases opposite with ⟨la, rb⟩ | ⟨lb, ra⟩
      · simpa only [la, rb] using across
      · rw [lb, ra, inner_sub_left]
        rw [inner_sub_left] at across
        exact fun h => across (by linarith only [h])
    have cross : orient 0 join d ≠ 0 := by
      intro collinear
      obtain ⟨s, eq⟩ := exists_lineMap_of_orient_eq_zero
        (K.projectedIntervalRay_ne_zero c i.castSucc.succ).symm collinear
      rw [AffineMap.lineMap_apply_module'] at eq
      simp only [sub_zero, add_zero] at eq
      apply d_diff
      rw [eq, real_inner_smul_right, tie, mul_zero]
    have shared : K.spatialDirection l join = K.spatialDirection r join := by
      rw [inner_sub_left, sub_eq_zero] at tie
      rw [K.spatialDirection_eq_section, K.spatialDirection_eq_section, tie]
    have total := c.sum_initial_suffix i intrinsic
    change |π - ∑ j, intrinsic (c.point j)| ≤
      sin φ * angle (K.spatialDirection l d) (K.spatialDirection r d)
    rw [total, left_angles, right_angles, L_first, L_last, R_first, R_last,
      scale, scale, neg, ← shared, angle_smul_left_of_pos _ _ ht,
      angle_smul_right_of_pos _ _ hu, angle_neg_right, angle_comm (K.spatialDirection l d)]
    have sharp := K.abs_spatialDirection_common_angle_sub_le_sin_tilt_of_transverse
      nonnegative small tilt l r join d shared cross
    dsimp only at sharp
    convert sharp using 1
    rw [abs_sub_comm]
    congr 1
    ring
  · have constant (j : Fin (n + 1)) : f j = f 0 := by
      refine Fin.induction rfl (fun i prev => ?_) j
      have same : f i.castSucc = f i.succ := by
        by_contra h
        exact changed ⟨i, h⟩
      exact same.symm.trans prev
    have angles := K.sum_flat_link_corner_angles c l constant
      (K.projectedInterval_halfplane_of_sum_le_pi c projected.le)
    rw [angles, first, last, scale, scale, neg, angle_smul_left_of_pos _ _ ht,
      angle_smul_right_of_pos _ _ hu, angle_neg_right,
      angle_self (K.spatialDirection_ne_zero l genuine), sub_zero, sub_self, abs_zero]
    exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos]))
      (angle_nonneg _ _)

end Unfoldings.ConvexCap
