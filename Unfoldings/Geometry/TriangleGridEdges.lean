module

public import Unfoldings.Geometry.TriangleGridCover

/-! The small-grid triangle edges are translations of the three original edge directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellCorners_eq_translate (a b c : E) (q i j : ℕ) (upper : Bool) :
    let z := point a b c q i j
    let u := (q : ℝ)⁻¹ • (b - a)
    let v := (q : ℝ)⁻¹ • (c - a)
    cellCorners a b c q i j upper =
      if upper then ![z + u + v, z + v, z + u] else ![z, z + u, z + v] := by
  dsimp only
  funext k
  cases upper <;> fin_cases k <;>
    simp [cellCorners, point, corner, Nat.cast_add, add_div] <;> module

omit [NormedSpace ℝ E] in
private theorem norm_translated_edges {z u v : E} {L : ℝ}
    (hu : ‖u‖ = L) (hv : ‖v‖ = L) (hd : ‖u - v‖ = L)
    (i j : Fin 3) (different : i ≠ j) :
    ‖(![z, z + u, z + v] : Fin 3 → E) i - ![z, z + u, z + v] j‖ = L := by
  have aroundU : ‖z + u - z‖ = L := by rwa [add_sub_cancel_left]
  have aroundV : ‖z + v - z‖ = L := by rwa [add_sub_cancel_left]
  have across : ‖(z + u) - (z + v)‖ = L := by rwa [add_sub_add_left_eq_sub]
  fin_cases i <;> fin_cases j <;> norm_num at different
  · exact (norm_sub_rev z _).trans aroundU
  · exact (norm_sub_rev z _).trans aroundV
  · exact aroundU
  · exact across
  · exact aroundV
  · exact (norm_sub_rev _ _).trans across

/-- Any two different corners have the same edge length when the grid is equilateral. -/
theorem norm_cellCorners_sub (a b c : E) (q i j : ℕ) (upper : Bool) {L : ℝ}
    (hu : ‖(q : ℝ)⁻¹ • (b - a)‖ = L) (hv : ‖(q : ℝ)⁻¹ • (c - a)‖ = L)
    (hd : ‖(q : ℝ)⁻¹ • (b - a) - (q : ℝ)⁻¹ • (c - a)‖ = L)
    (k l : Fin 3) (different : k ≠ l) :
    ‖cellCorners a b c q i j upper k - cellCorners a b c q i j upper l‖ = L := by
  rw [cellCorners_eq_translate]
  let z := point a b c q i j
  let u := (q : ℝ)⁻¹ • (b - a)
  let v := (q : ℝ)⁻¹ • (c - a)
  cases upper
  · exact norm_translated_edges hu hv hd k l different
  · let w := z + u + v
    have normal : (![z + u + v, z + v, z + u] : Fin 3 → E) =
        ![w, w + -u, w + -v] := by
      funext k
      fin_cases k <;> dsimp only [w] <;> abel
    simp only [ite_true]
    change ‖(![z + u + v, z + v, z + u] : Fin 3 → E) k - _‖ = L
    rw [normal]
    exact norm_translated_edges (by simpa only [norm_neg] using hu)
      (by simpa only [norm_neg] using hv)
      (by rw [show -u - -v = -(u - v) by abel, norm_neg]; exact hd) k l different

end Unfoldings.TriangleGrid
