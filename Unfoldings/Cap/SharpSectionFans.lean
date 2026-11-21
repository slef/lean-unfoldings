module

public import Unfoldings.Cap.SharpSectionHinge
public import Unfoldings.Cap.SharpAngleProjection
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Unfoldings.Cap.ProjectedInterval
public import Unfoldings.Cap.CreaseLinkSupport
public import Unfoldings.Geometry.LinearHalfplaneFan
public import Unfoldings.Geometry.ShortOrientedFan

/-! Intrinsic angles of subdivided halfplane fans and the sharp two-plane turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem sum_spatialDirection_ray_angles_eq_endpoint {n : ℕ} (f : Face)
    (ray : Fin (n + 2) → Plane) (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (halfplane : ∀ i, 0 ≤ orient 0 (ray 0) (ray i) *
      orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)) :
    (∑ i : Fin (n + 1),
      angle (K.spatialDirection f (ray i.castSucc)) (K.spatialDirection f (ray i.succ))) =
      angle (K.spatialDirection f (ray 0)) (K.spatialDirection f (ray (Fin.last (n + 1)))) := by
  let F := (K.folding.place f).linearIsometry
  let L := (K.projectFaceEquiv f).linear.symm
  change (∑ i : Fin (n + 1), angle (F (L (ray i.castSucc))) (F (L (ray i.succ)))) =
    angle (F (L (ray 0))) (F (L (ray (Fin.last (n + 1)))))
  simp only [LinearIsometry.angle_map]
  exact sum_linear_map_ray_angles_eq_endpoint L ray genuine nonzero consistent halfplane

/-- A straight bank split at either ray of its genuine seam pays the sine-scaled bend.
The two inputs are the endpoint angles of its two planar portions. -/
theorem abs_two_plane_fan_turn_le_sin_tilt {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (s : C.Seam) (d : Plane) (transverse : orient 0 (K.projectedSeamVector s) d ≠ 0) :
    let e := K.spatialDirection (C.left s).face (K.projectedSeamVector s)
    let a := K.spatialDirection (C.left s).face d
    let b := K.spatialDirection (C.right s).face d
    (|π - (angle a e + angle e (-b))| ≤ sin phi * angle a b) ∧
    (|π - (angle a (-e) + angle (-e) (-b))| ≤ sin phi * angle a b) := by
  dsimp only
  have bound := K.abs_spatialDirection_seam_angle_sub_le_sin_tilt_of_transverse
    nonnegative small tilt s d transverse
  dsimp only at bound
  constructor
  · rw [angle_neg_right, angle_comm (K.spatialDirection (C.left s).face d)]
    convert bound using 1
    rw [abs_sub_comm]
    congr 1
    ring
  · rw [angle_neg_neg, angle_neg_right, angle_comm (K.spatialDirection (C.left s).face d)]
    convert bound using 1
    congr 1
    ring

private theorem cos_ratio_eq_tan_half_sq {φ : ℝ} (positive : 0 < cos φ) :
    (1 - cos φ) / (1 + cos φ) = tan (φ / 2) ^ 2 := by
  have cp : 0 < 1 + cos φ := by positivity
  have ct : 0 < 1 + tan (φ / 2) ^ 2 := by positivity
  have identity := (eq_div_iff ct.ne').mp
    (cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq φ (by linarith only [positive]))
  exact (div_eq_iff cp.ne').mpr (by linarith only [identity])

/-- Even after subdivision, a corner sector contained in one supporting plane
pays exactly the one-face distortion bound. -/
theorem abs_spatialDirection_angle_error_le_sharp {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (f : Face) {a b : Plane} (ane : a ≠ 0) (bne : b ≠ 0) :
    |angle (K.spatialDirection f a) (K.spatialDirection f b) - angle a b| ≤
      2 * arcsin (tan (φ / 2) ^ 2) := by
  have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos], small⟩
  have h := Cap.tangent_projection_angle_error (K.normal_unit f) cp (tilt f)
    (K.spatialDirection_ne_zero f ane) (K.spatialDirection_ne_zero f bne)
    (K.spatialDirection_tangent f a) (K.spatialDirection_tangent f b)
  rwa [K.horizontal_spatialDirection, K.horizontal_spatialDirection, abs_sub_comm,
    cos_ratio_eq_tan_half_sq cp] at h

section ActualLink

variable {w : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ w).Chain n)

private theorem planar_arc_cones_disjoint :
    Pairwise (fun i j : Fin (n + 1) => Disjoint
      (strictRayCone (K.projectedIntervalRay c i.castSucc) (K.projectedIntervalRay c i.succ))
      (strictRayCone (K.projectedIntervalRay c j.castSucc) (K.projectedIntervalRay c j.succ))) := by
  intro i j different
  rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_cone, K.projectedGermRay_cone]
  have face_ne : (c.point i).val.1.1 ≠ (c.point j).val.1.1 := by
    intro eq
    apply different
    let a : C.CornerAt Set.univ w := ⟨(c.point i).val.1, (c.point i).property⟩
    let b : C.CornerAt Set.univ w := ⟨(c.point j).val.1, (c.point j).property⟩
    have same : a = b := K.cornerAt_face_injective w eq
    have faces := congrArg Subtype.val same
    rcases (C.germ_corner_eq_iff _ _).mp faces with eq | eq
    · exact c.injective (Subtype.ext eq)
    · exact (c.disjoint i j (Subtype.ext eq)).elim
  apply (K.projectedTriangle _).disjoint_cornerDirections (K.projectedTriangle _)
    (c.point i).val.1.2 (c.point j).val.1.2
  · exact (K.projectedGerm_apex (c.point i)).trans (K.projectedGerm_apex (c.point j)).symm
  · exact K.projectedTriangles_nonoverlapping face_ne

/-- The actual halfplane condition follows whenever the angle sum of this
link block is at most a half-turn. -/
theorem projectedInterval_halfplane_of_sum_le_pi
    (short : (∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π) :
    ∀ i, 0 ≤ orient 0 (K.projectedIntervalRay c 0) (K.projectedIntervalRay c i) *
      orient 0 (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc)
        (K.projectedIntervalRay c (0 : Fin (n + 1)).succ) := by
  let ray := K.projectedIntervalRay c
  have nonzero (i : Fin (n + 1)) : orient 0 (ray i.castSucc) (ray i.succ) ≠ 0 := by
    simp only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero (c.point i)
  exact orient_mul_nonneg_of_sum_ray_angles_le_pi ray (K.projectedIntervalRay_ne_zero c 0)
    nonzero (interval_cone_orient_sign ray nonzero (K.planar_arc_cones_disjoint c)) (by
      simpa only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
        K.projectedGermRay_angle] using short)

/-- At a regular transverse connector contact the ordered fan can switch
between its two supporting planes at most once. -/
theorem slope_change_index_unique {a b : Plane}
    (slopes : ∀ i, K.normalSlope (c.point i).val.1.1 = a ∨
      K.normalSlope (c.point i).val.1.1 = b)
    (transverse : inner ℝ (a - b) (K.projectedIntervalRay c 0) ≠ 0)
    (short : (∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π)
    {i j : Fin n}
    (i_change : K.normalSlope (c.point i.castSucc).val.1.1 ≠
      K.normalSlope (c.point i.succ).val.1.1)
    (j_change : K.normalSlope (c.point j.castSucc).val.1.1 ≠
      K.normalSlope (c.point j.succ).val.1.1) : i = j := by
  let ray := K.projectedIntervalRay c
  have nonzero (i : Fin (n + 1)) : orient 0 (ray i.castSucc) (ray i.succ) ≠ 0 := by
    simp only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero (c.point i)
  have tie (k : Fin n)
      (changes : K.normalSlope (c.point k.castSucc).val.1.1 ≠
        K.normalSlope (c.point k.succ).val.1.1) :
      inner ℝ (a - b) (ray k.castSucc.succ) = 0 := by
    have h := K.projectedIntervalRay_normalSlope_tie c k
    rcases slopes k.castSucc with la | lb <;> rcases slopes k.succ with ra | rb
    · exact (changes (la.trans ra.symm)).elim
    · simpa only [la, rb] using h
    · rw [lb, ra, inner_sub_left] at h
      rw [inner_sub_left]
      linarith only [h]
    · exact (changes (lb.trans rb.symm)).elim
  have equal := eq_indices_of_inner_zero_short_fan ray (K.projectedIntervalRay_ne_zero c) nonzero
    (interval_cone_orient_sign ray nonzero (K.planar_arc_cones_disjoint c)) (by
      simpa only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
        K.projectedGermRay_angle] using short) transverse (tie i i_change) (tie j j_change)
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [Fin.val_succ, Fin.val_castSucc] at values
  omega

/-- A short corner fan with an initial ray along the crease stays in its first
supporting plane. Any change would revisit the crease line at an interior ray. -/
theorem slope_constant_of_crease_first_short_fan {a b : Plane}
    (slopes : ∀ i, K.normalSlope (c.point i).val.1.1 = a ∨
      K.normalSlope (c.point i).val.1.1 = b)
    (tangent : inner ℝ (a - b) (K.projectedIntervalRay c 0) = 0)
    (short : (∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π) :
    ∀ i, K.normalSlope (c.point i).val.1.1 = K.normalSlope c.first.val.1.1 := by
  let ray := K.projectedIntervalRay c
  let f (i : Fin (n + 1)) := K.normalSlope (c.point i).val.1.1
  have genuine := K.projectedIntervalRay_ne_zero c
  have nonzero (i : Fin (n + 1)) : orient 0 (ray i.castSucc) (ray i.succ) ≠ 0 := by
    simp only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero (c.point i)
  have order := strictMono_angle_first_of_short_fan ray genuine nonzero
    (interval_cone_orient_sign ray nonzero (K.planar_arc_cones_disjoint c)) (by
      simpa only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
        K.projectedGermRay_angle] using short)
  have adjacent (k : Fin n) : f k.castSucc = f k.succ := by
    by_contra different
    have ab : a ≠ b := by
      intro same
      have all (j : Fin (n + 1)) : f j = b := (slopes j).elim (fun h => h.trans same) id
      exact different ((all _).trans (all _).symm)
    let j := k.castSucc.succ
    have tied : inner ℝ (a - b) (ray j) = 0 := by
      have h := K.projectedIntervalRay_normalSlope_tie c k
      rcases slopes k.castSucc with lp | lp <;> rcases slopes k.succ with rp | rp
      · exact (different (lp.trans rp.symm)).elim
      · simpa only [lp, rp] using h
      · rw [lp, rp, inner_sub_left] at h
        rw [inner_sub_left]
        linarith only [h]
      · exact (different (lp.trans rp.symm)).elim
    have cross := orient_zero_of_orthogonal_pair (sub_ne_zero.mpr ab) tangent tied
    obtain ⟨t, position⟩ := exists_lineMap_of_orient_eq_zero (genuine 0).symm cross
    rw [AffineMap.lineMap_apply_module'] at position
    simp only [sub_zero, add_zero] at position
    change ray j = t • ray 0 at position
    have tn : t ≠ 0 := by
      intro zero
      apply genuine j
      change ray j = 0
      rw [position, zero, zero_smul]
    have after : 0 < j := by change 0 < k.val + 1; omega
    have before : j < Fin.last (n + 1) := by
      change k.val + 1 < n + 1
      have h := k.isLt
      omega
    have positive : angle (ray 0) (ray 0) < angle (ray 0) (ray j) := order after
    have small : angle (ray 0) (ray j) < π := (order before).trans_le (angle_le_pi _ _)
    rcases lt_or_gt_of_ne tn with negative | positive_t
    · rw [position, angle_smul_right_of_neg _ _ negative, angle_neg_right,
        angle_self (genuine 0), sub_zero] at small
      exact lt_irrefl _ small
    · rw [position, angle_smul_right_of_pos _ _ positive_t,
        angle_self (genuine 0)] at positive
      exact lt_irrefl _ positive
  intro i
  exact Fin.induction rfl (fun k prev => (adjacent k).symm.trans prev) i

/-- In one supporting plane, the actual link's halfplane block has exactly the
spatial endpoint angle, independently of how the block was subdivided. -/
theorem sum_flat_link_corner_angles (f : Face)
    (slope : ∀ i, K.normalSlope (c.point i).val.1.1 = K.normalSlope f)
    (halfplane : ∀ i, 0 ≤ orient 0 (K.projectedIntervalRay c 0) (K.projectedIntervalRay c i) *
      orient 0 (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc)
        (K.projectedIntervalRay c (0 : Fin (n + 1)).succ)) :
    (∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      angle (K.spatialDirection f (K.projectedIntervalRay c 0))
        (K.spatialDirection f (K.projectedIntervalRay c (Fin.last (n + 1)))) := by
  let ray := K.projectedIntervalRay c
  have nonzero (i : Fin (n + 1)) : orient 0 (ray i.castSucc) (ray i.succ) ≠ 0 := by
    dsimp only [ray]
    rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero (c.point i)
  have sum := K.sum_spatialDirection_ray_angles_eq_endpoint f ray
    (K.projectedIntervalRay_ne_zero c) nonzero
    (interval_cone_orient_sign ray nonzero (K.planar_arc_cones_disjoint c)) halfplane
  rw [← sum]
  apply Finset.sum_congr rfl
  intro i _
  have recover (p : C.LinkGerm Set.univ w) (same : K.normalSlope p.val.1.1 = K.normalSlope f) :
      K.spatialDirection f (K.projectedGermRay p) = K.folding.germDirection p.val := by
    rw [← K.horizontal_germDirection]
    calc
      _ = K.spatialDirection p.val.1.1 (Cap.horizontal (K.folding.germDirection p.val)) := by
        rw [K.spatialDirection_eq_section, K.spatialDirection_eq_section, same]
      _ = _ := K.spatialDirection_horizontal_germ p.val
  change _ = angle (K.spatialDirection f (K.projectedIntervalRay c i.castSucc))
    (K.spatialDirection f (K.projectedIntervalRay c i.succ))
  rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    recover (c.point i) (slope i), recover (C.linkTurn Set.univ w (c.point i)) (slope i)]
  exact (K.folding.germDirection_angle (c.point i).val).symm

/-- The actual spatial and projected angles of a flat link block differ by
one sharp face error, however many triangles meet at the vertex. -/
theorem abs_flat_link_projection_error_le_sharp {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (f : Face) (slope : ∀ i, K.normalSlope (c.point i).val.1.1 = K.normalSlope f)
    (halfplane : ∀ i, 0 ≤ orient 0 (K.projectedIntervalRay c 0) (K.projectedIntervalRay c i) *
      orient 0 (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc)
        (K.projectedIntervalRay c (0 : Fin (n + 1)).succ)) :
    |(∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i : Fin (n + 1), (K.projectedTriangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  let ray := K.projectedIntervalRay c
  have genuine := K.projectedIntervalRay_ne_zero c
  have nonzero (i : Fin (n + 1)) : orient 0 (ray i.castSucc) (ray i.succ) ≠ 0 := by
    dsimp only [ray]
    rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.projectedGermRay_orient_ne_zero (c.point i)
  have flat := sum_ray_angles_eq_endpoint ray genuine nonzero
    (interval_cone_orient_sign ray nonzero (K.planar_arc_cones_disjoint c)) halfplane
  simp only [ray, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_angle] at flat
  rw [K.sum_flat_link_corner_angles c f slope halfplane, flat]
  exact K.abs_spatialDirection_angle_error_le_sharp nonnegative small tilt f (genuine 0)
    (genuine (Fin.last (n + 1)))

end ActualLink

end Unfoldings.ConvexCap
