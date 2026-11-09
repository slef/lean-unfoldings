module

public import Mathlib.Analysis.InnerProductSpace.Affine
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Real affine coordinates on a genuine line, for finite segment subdivision. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lineCoordinate (a b : E) : E →ᵃ[ℝ] ℝ :=
  ⟪b - a, b - a⟫⁻¹ • ((innerₛₗ ℝ (b - a)).toAffineMap.comp
    (AffineMap.id ℝ E - AffineMap.const ℝ E a))

theorem lineCoordinate_apply (a b x : E) :
    lineCoordinate a b x = ⟪b - a, b - a⟫⁻¹ * ⟪b - a, x - a⟫ := rfl

theorem lineCoordinate_lineMap {a b : E} (different : a ≠ b) (t : ℝ) :
    lineCoordinate a b (AffineMap.lineMap a b t) = t := by
  rw [lineCoordinate_apply, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, inner_smul_right]
  rw [mul_left_comm,
    inv_mul_cancel₀ (inner_self_ne_zero.mpr (sub_ne_zero.mpr different.symm)), mul_one]

theorem lineCoordinate_recover {a b x : E} (different : a ≠ b)
    (member : x ∈ affineSpan ℝ ({a, b} : Set E)) :
    AffineMap.lineMap a b (lineCoordinate a b x) = x := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp member
  rw [lineCoordinate_lineMap different]

theorem lineCoordinate_injective {a b : E} (different : a ≠ b) :
    Set.InjOn (lineCoordinate a b) (affineSpan ℝ ({a, b} : Set E)) := by
  intro x hx y hy equal
  rw [← lineCoordinate_recover different hx, ← lineCoordinate_recover different hy, equal]

theorem lineCoordinate_mem_segment_iff {a b c d x : E} (different : a ≠ b)
    (hc : c ∈ affineSpan ℝ ({a, b} : Set E)) (hd : d ∈ affineSpan ℝ ({a, b} : Set E))
    (hx : x ∈ affineSpan ℝ ({a, b} : Set E)) :
    x ∈ segment ℝ c d ↔ lineCoordinate a b x ∈
      Set.uIcc (lineCoordinate a b c) (lineCoordinate a b d) := by
  have image := image_segment ℝ (lineCoordinate a b) c d
  rw [segment_eq_uIcc] at image
  constructor
  · intro member
    rw [← image]
    exact ⟨x, member, rfl⟩
  · intro member
    rw [← image] at member
    obtain ⟨y, hy, equal⟩ := member
    have hy_line := (affineSpan ℝ ({a, b} : Set E)).convex.segment_subset hc hd hy
    have same := lineCoordinate_injective different hy_line hx equal
    exact same ▸ hy

theorem lineCoordinate_mem_openSegment_iff {a b c d x : E} (different : a ≠ b)
    (ends : c ≠ d) (hc : c ∈ affineSpan ℝ ({a, b} : Set E))
    (hd : d ∈ affineSpan ℝ ({a, b} : Set E)) (hx : x ∈ affineSpan ℝ ({a, b} : Set E)) :
    x ∈ openSegment ℝ c d ↔ lineCoordinate a b x ∈
      Set.Ioo (min (lineCoordinate a b c) (lineCoordinate a b d))
        (max (lineCoordinate a b c) (lineCoordinate a b d)) := by
  have unequal : lineCoordinate a b c ≠ lineCoordinate a b d :=
    fun equal => ends (lineCoordinate_injective different hc hd equal)
  have image := image_openSegment ℝ (lineCoordinate a b) c d
  rw [openSegment_eq_Ioo' unequal] at image
  constructor
  · intro member
    rw [← image]
    exact ⟨x, member, rfl⟩
  · intro member
    rw [← image] at member
    obtain ⟨y, hy, equal⟩ := member
    have hy_line := (affineSpan ℝ ({a, b} : Set E)).convex.segment_subset hc hd
      (openSegment_subset_segment ℝ c d hy)
    have same := lineCoordinate_injective different hy_line hx equal
    exact same ▸ hy

end Unfoldings
