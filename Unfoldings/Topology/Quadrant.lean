module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Basic.NNReal.Defs

/-!
# A quadrant and a half-plane have the same topology

The piecewise linear map `(x,y) ↦ (x-y,min x y)` opens a quadrant into a
half-plane. Its inverse is `(u,v) ↦ (max u 0+v,max (-u) 0+v)`. The two outer
rays become the two halves of the boundary line, and the apex remains fixed.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.PlanarTopology

def closedQuadrant : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

def closedHalfPlane : Set (ℝ × ℝ) := {p | 0 ≤ p.2}

def quadrantHalfPlaneHomeomorph : closedQuadrant ≃ₜ closedHalfPlane where
  toFun p := ⟨(p.val.1 - p.val.2, min p.val.1 p.val.2), le_min p.property.1 p.property.2⟩
  invFun p := ⟨(max p.val.1 0 + p.val.2, max (-p.val.1) 0 + p.val.2),
    add_nonneg (le_max_right _ _) p.property, add_nonneg (le_max_right _ _) p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    all_goals
      rw [min_def, max_def]
      split_ifs <;> linarith
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    all_goals
      simp only [min_def, max_def]
      split_ifs <;> linarith
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem quadrantHalfPlaneHomeomorph_zero :
    quadrantHalfPlaneHomeomorph ⟨(0, 0), by constructor <;> rfl⟩ =
      ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  apply Subtype.ext
  simp [quadrantHalfPlaneHomeomorph]

@[simp] theorem quadrantHalfPlaneHomeomorph_firstRay (r : ℝ≥0) :
    quadrantHalfPlaneHomeomorph ⟨((r : ℝ), 0), by exact ⟨r.property, le_refl 0⟩⟩ =
      ⟨((r : ℝ), 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  apply Subtype.ext
  simp [quadrantHalfPlaneHomeomorph]

@[simp] theorem quadrantHalfPlaneHomeomorph_secondRay (r : ℝ≥0) :
    quadrantHalfPlaneHomeomorph ⟨(0, (r : ℝ)), by exact ⟨le_refl 0, r.property⟩⟩ =
      ⟨(-(r : ℝ), 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  apply Subtype.ext
  simp [quadrantHalfPlaneHomeomorph]

theorem quadrantHalfPlaneHomeomorph_boundary (p : closedQuadrant) :
    (quadrantHalfPlaneHomeomorph p).val.2 = 0 ↔ p.val.1 = 0 ∨ p.val.2 = 0 := by
  change min p.val.1 p.val.2 = 0 ↔ _
  rw [min_eq_iff]
  constructor
  · rintro (⟨equal, _⟩ | ⟨equal, _⟩)
    · exact Or.inl equal
    · exact Or.inr equal
  · rintro (equal | equal)
    · exact Or.inl ⟨equal, by simpa only [equal] using p.property.2⟩
    · exact Or.inr ⟨equal, by simpa only [equal] using p.property.1⟩

end Unfoldings.PlanarTopology
