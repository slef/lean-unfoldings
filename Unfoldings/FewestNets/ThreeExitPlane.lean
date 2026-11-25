module

public import Unfoldings.FewestNets.ThreeExitSeparation
public import Unfoldings.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.FinCases

/-! Interpret the three-exit reachability constraints in the planar slope chart. -/

@[expose] public section

namespace Unfoldings.FewestNets.ThreeExitChoices

open Relation

private def coords (p : Plane) : ℝ × ℝ := (p 0, p 1)

private theorem coords_injective : Function.Injective coords := by
  intro p q h
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

private theorem coords_lineMap (p q : Plane) (t : ℝ) :
    coords (AffineMap.lineMap p q t) = ((1 - t) * p 0 + t * q 0, (1 - t) * p 1 + t * q 1) := by
  rw [AffineMap.lineMap_apply_module]
  rfl

private theorem coords_ray (p d : Plane) {u : ℝ} (nonzero : d 0 ≠ 0) :
    coords (p + ((u - p 0) / d 0) • d) = (u, p 1 + (d 1 / d 0) * (u - p 0)) := by
  apply Prod.ext
  · change p 0 + ((u - p 0) / d 0) * d 0 = u
    rw [div_mul_cancel₀ _ nonzero]
    ring
  · change p 1 + ((u - p 0) / d 0) * d 1 = p 1 + (d 1 / d 0) * (u - p 0)
    ring

variable {V : Type*}

/-- Two open rays supplied at the forced roots rule out a conflicting path in
a straight planar realization. The height used for parent ascent is north. -/
theorem no_path_of_plane_rays (R : ThreeExitChoices V) (p : V → Plane)
    (height : ∀ v, R.height v = p v 1) (carrier : Set Plane)
    (east west : Plane) (east_pos : 0 < east 0) (west_neg : west 0 < 0)
    (edges : ∀ ⦃v w⦄, R.constraint v w → segment ℝ (p v) (p w) ⊆ carrier)
    (east_forward : ∀ v ∉ R.boundary, p v 0 < p (R.eastParent v) 0)
    (west_backward : ∀ v ∉ R.boundary, p (R.westParent v) 0 < p v 0)
    (east_avoids : ∀ r, R.forcedEast r → ∀ t > (0 : ℝ), p r + t • east ∉ carrier)
    (west_avoids : ∀ s, R.forcedWest s → ∀ t > (0 : ℝ), p s + t • west ∉ carrier)
    (east_enters : ∀ r, R.forcedEast r → ∀ v ∉ R.boundary, R.westParent v = r →
      p v 1 - p r 1 < (east 1 / east 0) * (p v 0 - p r 0))
    (west_enters : ∀ s, R.forcedWest s → ∀ v ∉ R.boundary, R.eastParent v = s →
      p v 1 - p s 1 < (west 1 / west 0) * (p v 0 - p s 0))
    (separate : ∀ r s, R.forcedEast r → R.forcedWest s → ∀ a b : ℝ, 0 < a → 0 < b →
      p r + a • east ≠ p s + b • west) :
    ∀ r s, R.forcedEast r → R.forcedWest s → ¬ ReflTransGen R.constraint r s := by
  refine R.no_path_of_exterior_rays (fun v => p v 0) (coords '' carrier)
    (fun _ => east 1 / east 0) (fun _ => west 1 / west 0) ?_ east_forward west_backward
    ?_ ?_ ?_ ?_ ?_
  · intro v w step t nonneg upper
    refine ⟨AffineMap.lineMap (p v) (p w) t,
      edges step (lineMap_mem_segment ℝ _ _ ⟨nonneg, upper⟩), ?_⟩
    simp only [height, coords_lineMap]
  · intro r forced u right
    rw [height, ← coords_ray (p r) east east_pos.ne']
    rintro ⟨z, in_carrier, same⟩
    exact east_avoids r forced _ (div_pos (sub_pos.mpr right) east_pos)
      (coords_injective same ▸ in_carrier)
  · intro s forced u left
    rw [height, ← coords_ray (p s) west west_neg.ne]
    rintro ⟨z, in_carrier, same⟩
    exact west_avoids s forced _ (div_pos_of_neg_of_neg (sub_neg.mpr left) west_neg)
      (coords_injective same ▸ in_carrier)
  · intro r forced v interior parent
    rw [height, height]
    linarith only [east_enters r forced v interior parent]
  · intro s forced v interior parent
    rw [height, height]
    linarith only [west_enters s forced v interior parent]
  · intro r s forcedEast forcedWest u left right equal
    apply separate r s forcedEast forcedWest ((u - p r 0) / east 0) ((u - p s 0) / west 0)
      (div_pos (sub_pos.mpr left) east_pos) (div_pos_of_neg_of_neg (sub_neg.mpr right) west_neg)
    apply coords_injective
    simp only [height] at equal
    rw [coords_ray (p r) east east_pos.ne', coords_ray (p s) west west_neg.ne]
    exact Prod.ext rfl equal

end Unfoldings.FewestNets.ThreeExitChoices
