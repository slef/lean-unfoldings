module

public import Unfoldings.Topology.Quadrant
public import Unfoldings.Topology.BoundaryPush

/-!
# An explicit local inward push on a half-plane

A compactly supported vertical push is injective, keeps interior points in
the interior, and moves exactly a bounded boundary interval into the interior.
Its support and image stay in the same rectangle, so it can be transferred
through a local boundary chart and extended by the identity.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

def boundaryBump (u : ℝ) : ℝ := max 0 (1 - |u|) / 2

theorem boundaryBump_nonneg (u : ℝ) : 0 ≤ boundaryBump u :=
  div_nonneg (le_max_left _ _) (by norm_num)

theorem boundaryBump_lt_one (u : ℝ) : boundaryBump u < 1 := by
  have bound : max 0 (1 - |u|) ≤ 1 := max_le (by norm_num) (by linarith [abs_nonneg u])
  unfold boundaryBump
  linarith

theorem boundaryBump_pos_iff (u : ℝ) : 0 < boundaryBump u ↔ |u| < 1 := by
  unfold boundaryBump
  rw [div_pos_iff_of_pos_right (by norm_num)]
  simp only [lt_max_iff, lt_self_iff_false, false_or, sub_pos]

@[simp] theorem boundaryBump_zero_iff (u : ℝ) : boundaryBump u = 0 ↔ 1 ≤ |u| := by
  constructor
  · intro equal
    by_contra outside
    have positive := (boundaryBump_pos_iff u).mpr (lt_of_not_ge outside)
    rw [equal] at positive
    exact lt_irrefl 0 positive
  · intro outside
    apply le_antisymm _ (boundaryBump_nonneg u)
    exact le_of_not_gt (fun positive =>
      (not_lt_of_ge outside) ((boundaryBump_pos_iff u).mp positive))

theorem continuous_boundaryBump : Continuous boundaryBump := by
  unfold boundaryBump
  fun_prop

def raisedHeight (a t : ℝ) : ℝ := t + a * max 0 (1 - t)

theorem raisedHeight_strictMono {a : ℝ} (nonnegative : 0 ≤ a) (small : a < 1) :
    StrictMono (raisedHeight a) := by
  intro s t less
  unfold raisedHeight
  simp only [max_def]
  split_ifs <;> nlinarith

theorem raisedHeight_nonneg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 ≤ raisedHeight a t := add_nonneg ht (mul_nonneg ha (le_max_left _ _))

theorem raisedHeight_lt_one_iff {a t : ℝ} (ha : 0 ≤ a) (small : a < 1) :
    raisedHeight a t < 1 ↔ t < 1 := by
  have fixed : raisedHeight a 1 = 1 := by simp [raisedHeight]
  calc
    raisedHeight a t < 1 ↔ raisedHeight a t < raisedHeight a 1 := by rw [fixed]
    _ ↔ t < 1 := (raisedHeight_strictMono ha small).lt_iff_lt

def inwardPush : closedHalfPlane → closedHalfPlane := fun p =>
  ⟨(p.val.1, raisedHeight (boundaryBump p.val.1) p.val.2),
    raisedHeight_nonneg (boundaryBump_nonneg _) p.property⟩

theorem continuous_inwardPush : Continuous inwardPush := by
  unfold inwardPush raisedHeight boundaryBump
  fun_prop

theorem inwardPush_injective : Function.Injective inwardPush := by
  intro p q equal
  have first := congrArg (fun x : closedHalfPlane => x.val.1) equal
  change p.val.1 = q.val.1 at first
  have heights := congrArg (fun x : closedHalfPlane => x.val.2) equal
  change raisedHeight (boundaryBump p.val.1) p.val.2 =
    raisedHeight (boundaryBump q.val.1) q.val.2 at heights
  rw [← first] at heights
  apply Subtype.ext
  exact Prod.ext first
    ((raisedHeight_strictMono (boundaryBump_nonneg _) (boundaryBump_lt_one _)).injective heights)

theorem inwardPush_fixed_of_outside (p : closedHalfPlane)
    (outside : 1 ≤ |p.val.1| ∨ 1 ≤ p.val.2) : inwardPush p = p := by
  apply Subtype.ext
  change (p.val.1, raisedHeight (boundaryBump p.val.1) p.val.2) = p.val
  apply Prod.ext
  · rfl
  rcases outside with horizontal | vertical
  · simp only [(boundaryBump_zero_iff _).mpr horizontal,
      raisedHeight, zero_mul, add_zero]
  · simp only [raisedHeight, max_eq_left (sub_nonpos.mpr vertical),
      mul_zero, add_zero]

theorem inwardPush_positive_of_positive (p : closedHalfPlane) (inside : 0 < p.val.2) :
    0 < (inwardPush p).val.2 := by
  exact inside.trans_le (le_add_of_nonneg_right
    (mul_nonneg (boundaryBump_nonneg _) (le_max_left _ _)))

theorem inwardPush_boundary_positive (p : closedHalfPlane) (boundary : p.val.2 = 0) :
    0 < (inwardPush p).val.2 ↔ |p.val.1| < 1 := by
  change 0 < raisedHeight (boundaryBump p.val.1) p.val.2 ↔ _
  simp only [boundary, raisedHeight, sub_zero, max_eq_right zero_le_one, mul_one, zero_add]
  exact boundaryBump_pos_iff _

theorem inwardPush_boundary_fixed_or_positive (p : closedHalfPlane)
    (boundary : p.val.2 = 0) : inwardPush p = p ∨ 0 < (inwardPush p).val.2 := by
  by_cases small : |p.val.1| < 1
  · exact Or.inr ((inwardPush_boundary_positive p boundary).mpr small)
  · exact Or.inl (inwardPush_fixed_of_outside p (Or.inl (le_of_not_gt small)))

def pushRectangle : Set closedHalfPlane := {p | |p.val.1| < 1 ∧ p.val.2 < 1}

theorem isOpen_pushRectangle : IsOpen pushRectangle := by
  exact (isOpen_lt (continuous_subtype_val.fst.abs) continuous_const).inter
    (isOpen_lt continuous_subtype_val.snd continuous_const)

theorem inwardPush_mem_rectangle_iff (p : closedHalfPlane) :
    inwardPush p ∈ pushRectangle ↔ p ∈ pushRectangle := by
  change |p.val.1| < 1 ∧ raisedHeight (boundaryBump p.val.1) p.val.2 < 1 ↔ _
  rw [raisedHeight_lt_one_iff (boundaryBump_nonneg _) (boundaryBump_lt_one _)]
  rfl

theorem inwardPush_fixed_of_not_mem_rectangle (p : closedHalfPlane)
    (outside : p ∉ pushRectangle) : inwardPush p = p := by
  apply inwardPush_fixed_of_outside
  by_contra near
  push Not at near
  exact outside ⟨near.1, near.2⟩

def halfPlaneBoundary : Set closedHalfPlane := {p | p.val.2 = 0}

def standardBoundaryPush : BoundaryPush halfPlaneBoundary where
  map := ⟨inwardPush, continuous_inwardPush⟩
  injective := inwardPush_injective
  interior := by
    intro p outside
    change p.val.2 ≠ 0 at outside
    change (inwardPush p).val.2 ≠ 0
    exact (inwardPush_positive_of_positive p (lt_of_le_of_ne p.property (Ne.symm outside))).ne'
  boundary := fun p hp => inwardPush_boundary_fixed_or_positive p hp |>.imp_right
    (fun positive => positive.ne')

def pushSupport : Set closedHalfPlane := {p | |p.val.1| ≤ 1 ∧ p.val.2 ≤ 1}

theorem isCompact_pushSupport : IsCompact pushSupport := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have image : Subtype.val '' pushSupport = Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨abs_le.mp hq.1, q.property, hq.2⟩
    · rintro ⟨horizontal, vertical⟩
      exact ⟨⟨p, vertical.1⟩, ⟨abs_le.mpr horizontal, vertical.2⟩, rfl⟩
  rw [image]
  exact isCompact_Icc.prod isCompact_Icc

theorem inwardPush_fixed_of_not_mem_support (p : closedHalfPlane)
    (outside : p ∉ pushSupport) : inwardPush p = p := by
  apply inwardPush_fixed_of_not_mem_rectangle
  intro inside
  exact outside ⟨inside.1.le, inside.2.le⟩

theorem inwardPush_mapsTo_support : Set.MapsTo inwardPush pushSupport pushSupport := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  have fixed : raisedHeight (boundaryBump p.val.1) 1 = 1 := by simp [raisedHeight]
  exact ((raisedHeight_strictMono (boundaryBump_nonneg _) (boundaryBump_lt_one _)).monotone hp.2)
    |>.trans_eq fixed

end Unfoldings.PlanarTopology
