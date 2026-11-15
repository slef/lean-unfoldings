module

public import Unfoldings.Metric.PolygonalCut
public import Unfoldings.Metric.PhysicalSeamLabels
public import Unfoldings.Geometry.AffineArrangement

/-! A cut through an affine level separates its two actual metric banks locally. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E)

omit [Finite I] in
/-- A retained physical attachment cannot cross the two sides of a locally complete affine cut. -/
theorem cutSeams_sign_eq (f : E →ᵃ[ℝ] ℝ) (signs : I → Bool)
    (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
    {U : Set E} (open_U : IsOpen U)
    (cut_level : ∀ x ∈ U, f x = 0 → x ∈ cuts)
    {z : E} (inside : z ∈ U) (i j : I)
    (seam : z ∈ (cutSeams cells closed cuts).carrier i j) : signs i = signs j := by
  by_contra different
  have avoids : (cells i ∩ cells j) \ cuts ⊆ Uᶜ := by
    intro x hx inside_x
    have first := aligned i x hx.1.1
    have last := aligned j x hx.1.2
    have zero : f x = 0 := by
      cases hi : signs i <;> cases hj : signs j <;>
        simp_all [AffineArrangement.signed] <;> linarith
    exact hx.2 (cut_level x inside_x zero)
  exact closure_minimal avoids open_U.isClosed_compl seam inside

/-- Opposite banks remain distinct in the actual route metric, even with unbounded cells. -/
theorem cut_of_ne_of_opposite_sign (f : E →ᵃ[ℝ] ℝ) (signs : I → Bool)
    (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
    {U : Set E} (open_U : IsOpen U)
    (cut_level : ∀ x ∈ U, f x = 0 → x ∈ cuts)
    {i j : I} (x : cells i) (y : cells j) (inside : x.val ∈ U)
    (different : signs i ≠ signs j) :
    of (fun i => cells i) (cutSeams cells closed cuts).relation i x ≠
      of (fun i => cells i) (cutSeams cells closed cuts).relation j y := by
  exact (cutSeams cells closed cuts).of_ne_of_label_ne signs x.val
    (fun i j seam => cutSeams_sign_eq cells closed cuts f signs aligned open_U cut_level
      inside i j seam) x y rfl different

end Unfoldings.MetricGluing
