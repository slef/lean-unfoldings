module

public import Unfoldings.Cap.RoofLevels
public import Mathlib.Tactic.FieldSimp

/-!
# Compact horizontal clips of the actual unbounded roof

One positive cap height makes every lower horizontal clip bounded. A direct
homothety bound contains its footprint in a compact image of the original
footprint. No triangulation or cutting scheme is presumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def clipFootprint (Z : ℝ) : Set Plane := {p | Z ≤ K.roofHeight p}

theorem isClosed_clipFootprint (Z : ℝ) : IsClosed (K.clipFootprint Z) :=
  isClosed_Ici.preimage K.continuous_roofHeight

theorem convex_clipFootprint (Z : ℝ) : Convex ℝ (K.clipFootprint Z) := by
  simpa only [clipFootprint, Set.mem_univ, true_and] using K.roofHeight_concave.convex_ge Z

theorem footprint_subset_clip (Z : ℝ) (lower : Z ≤ 0) : K.footprint ⊆ K.clipFootprint Z :=
  fun _ inside => lower.trans (K.roofHeight_nonneg_of_mem inside)

/-- Each finite lower clip lies in an explicit homothetic image of the original footprint. -/
theorem clipFootprint_subset_homothety {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) :
    K.clipFootprint Z ⊆ (fun r => q + ((K.roofHeight q - Z) / K.roofHeight q) • (r - q)) ''
      K.footprint := by
  intro p inside
  let H := K.roofHeight q
  have H_pos : 0 < H := positive
  have denominator : 0 < H - Z := by linarith
  let s := H / (H - Z)
  have s_pos : 0 < s := div_pos H_pos denominator
  have s_le : s ≤ 1 := (div_le_one denominator).mpr (by linarith)
  let r := q + s • (p - q)
  have coefficient : (1 - s) * H + s * Z = 0 := by
    dsimp only [s]
    field_simp
    ring
  have concave := K.roofHeight_concave.2 (Set.mem_univ q) (Set.mem_univ p)
    (sub_nonneg.mpr s_le) s_pos.le (show (1 - s) + s = 1 by ring)
  have point : (1 - s) • q + s • p = r := by dsimp only [r]; module
  rw [point] at concave
  have roof_nonnegative : 0 ≤ K.roofHeight r := by
    change Z ≤ K.roofHeight p at inside
    change (1 - s) * H + s * K.roofHeight p ≤ K.roofHeight r at concave
    have variation := mul_le_mul_of_nonneg_left inside s_pos.le
    linarith
  have r_inside : r ∈ K.footprint := by
    rw [K.footprint_eq_roof_superlevel_zero member positive]
    exact roof_nonnegative
  refine ⟨r, r_inside, ?_⟩
  have inverse : ((H - Z) / H) * s = 1 := by
    dsimp only [s]
    field_simp
  change q + ((H - Z) / H) • (r - q) = p
  dsimp only [r]
  rw [add_sub_cancel_left, smul_smul, inverse, one_smul, add_sub_cancel]

/-- Positive-height caps have compact clips at every finite level below the original rim. -/
theorem isCompact_clipFootprint {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) :
    IsCompact (K.clipFootprint Z) := by
  have continuous : Continuous
      (fun r : Plane => q + ((K.roofHeight q - Z) / K.roofHeight q) • (r - q)) := by fun_prop
  exact (K.compact_footprint.image continuous).of_isClosed_subset (K.isClosed_clipFootprint Z)
    (K.clipFootprint_subset_homothety member positive lower)

theorem strict_level_mem_clip_interior {Z : ℝ} {p : Plane} (higher : Z < K.roofHeight p) :
    p ∈ interior (K.clipFootprint Z) := by
  let U : Set Plane := {p | Z < K.roofHeight p}
  have opens : IsOpen U := isOpen_lt continuous_const K.continuous_roofHeight
  have subset : U ⊆ K.clipFootprint Z := by
    intro x higher
    change Z < K.roofHeight x at higher
    exact higher.le
  apply interior_mono subset
  rw [opens.interior_eq]
  exact higher

theorem original_footprint_in_clip_interior {Z : ℝ} (lower : Z < 0) :
    K.footprint ⊆ interior (K.clipFootprint Z) :=
  fun _ member => K.strict_level_mem_clip_interior
    (lower.trans_le (K.roofHeight_nonneg_of_mem member))

/-- The actual boundary of each clip lies in its prescribed horizontal plane. -/
theorem roofHeight_eq_level_of_clip_frontier {Z : ℝ} {p : Plane}
    (boundary : p ∈ frontier (K.clipFootprint Z)) : K.roofHeight p = Z := by
  have member : p ∈ K.clipFootprint Z := (K.isClosed_clipFootprint Z).closure_eq ▸ boundary.1
  apply le_antisymm _ member
  by_contra higher
  exact boundary.2 (K.strict_level_mem_clip_interior (lt_of_not_ge higher))

def clippedRoof (Z : ℝ) : Set Space := K.roofPoint '' K.clipFootprint Z

theorem isCompact_clippedRoof {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) :
    IsCompact (K.clippedRoof Z) :=
  (K.isCompact_clipFootprint member positive lower).image K.continuous_roofPoint

theorem original_surface_subset_clippedRoof {Z : ℝ} (lower : Z ≤ 0) :
    K.folding.surface ⊆ K.clippedRoof Z := by
  intro z surface
  have actual := (K.surface_iff_roofHeight z).mp surface
  refine ⟨Cap.horizontal z, K.footprint_subset_clip Z lower actual.1, ?_⟩
  exact K.roofPoint_horizontal ⟨z, K.original_surface_subset_extendedRoof surface⟩

end Unfoldings.ConvexCap
