module

public import Unfoldings.Path.Length
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Length of straight paths in real normed spaces. -/

@[expose] public section

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem segment_lipschitz (a b : E) : LipschitzWith (nndist a b) (Path.segment a b) := by
  have inclusion : Isometry ((↑) : unitInterval → ℝ) := fun _ _ => rfl
  change LipschitzWith (nndist a b) (AffineMap.lineMap a b ∘ ((↑) : unitInterval → ℝ))
  simpa only [mul_one] using (lipschitzWith_lineMap a b (𝕜 := ℝ)).comp inclusion.lipschitzWith

@[simp] theorem eLength_segment (a b : E) : (Path.segment a b).eLength = edist a b := by
  apply le_antisymm
  · exact ((Path.segment a b).eLength_le_of_lipschitz (segment_lipschitz a b)).trans_eq
      (edist_nndist a b).symm
  · exact (Path.segment a b).edist_le_eLength

end Path
