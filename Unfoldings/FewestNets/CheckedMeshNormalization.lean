module

public import Unfoldings.FewestNets.CheckedMeshChart

/-! Actual maximum-radius normalization and its checked tangent coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

variable {n : ℕ} (star : MeshStar (n + 1))

/-- The maximum of the vertex radii over a supplied list. -/
def vertexRadiusOver : List (Fin (n + 1)) → ℝ
  | [] => 0
  | i :: rest => max ‖star.physicalVertex i‖ (vertexRadiusOver rest)

/-- The exact largest vertex norm in the unscaled physical tangent chart. -/
def maximumRadius : ℝ := star.vertexRadiusOver (List.finRange (n + 1))

private theorem norm_physicalVertex_le_radiusOver (indices : List (Fin (n + 1)))
    {i : Fin (n + 1)} (member : i ∈ indices) :
    ‖star.physicalVertex i‖ ≤ star.vertexRadiusOver indices := by
  induction indices with
  | nil => simp at member
  | cons j rest ih =>
    rw [vertexRadiusOver]
    rcases List.mem_cons.mp member with rfl | remaining
    · exact le_max_left _ _
    · exact (ih remaining).trans (le_max_right _ _)

theorem norm_physicalVertex_le_maximumRadius (i : Fin (n + 1)) :
    ‖star.physicalVertex i‖ ≤ star.maximumRadius :=
  star.norm_physicalVertex_le_radiusOver _ (List.mem_finRange i)

theorem maximumRadius_pos {i : Fin (n + 1)} (nonzero : star.physicalVertex i ≠ 0) :
    0 < star.maximumRadius :=
  (norm_pos_iff.mpr nonzero).trans_le (star.norm_physicalVertex_le_maximumRadius i)

def maximumNormalizedVertex (i : Fin (n + 1)) : Plane :=
  star.maximumRadius⁻¹ • star.physicalVertex i

def maximumNormalizedSideOffset (i : Fin (n + 1)) : ℝ :=
  star.physicalSideOffset i / star.maximumRadius

theorem norm_maximumNormalizedVertex_le_one (positive : 0 < star.maximumRadius) (i : Fin (n + 1)) :
    ‖star.maximumNormalizedVertex i‖ ≤ 1 := by
  rw [maximumNormalizedVertex, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
    ← div_eq_inv_mul, div_le_one positive]
  exact star.norm_physicalVertex_le_maximumRadius i

namespace Checked

variable {D : ℕ} {star} (hD : 0 < D) (a : Checked D star)

/-- Enclose the actual maximum rather than any derivative estimate. -/
def vertexRadiusOver : (indices : List (Fin (n + 1))) →
    CheckedReal D (star.vertexRadiusOver indices)
  | [] => (CheckedReal.rat D 0).convert (by simp [MeshStar.vertexRadiusOver])
  | i :: rest => (CheckedPlane.norm hD (a.physicalVertex hD i)).maximum hD (vertexRadiusOver rest)

def maximumRadius : CheckedReal D star.maximumRadius :=
  a.vertexRadiusOver hD (List.finRange (n + 1))

def maximumNormalizedVertex (i : Fin (n + 1)) : CheckedPlane D (star.maximumNormalizedVertex i) :=
  CheckedPlane.divide hD (a.physicalVertex hD i) (a.maximumRadius hD)

def maximumNormalizedSideOffset (i : Fin (n + 1)) :
    CheckedReal D (star.maximumNormalizedSideOffset i) :=
  (a.physicalSideOffset hD i).div hD (a.maximumRadius hD)

end Checked
end Unfoldings.FewestNets.MeshStar
