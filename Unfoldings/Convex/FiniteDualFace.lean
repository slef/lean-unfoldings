module

public import Unfoldings.Convex.FiniteDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-! Interior maximizing slopes identify exactly the original primal supporting face. -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Unfoldings.FiniteDual

variable {I : Type*} [Fintype I] [Nonempty I]
  (point : I → Plane) (level : I → ℝ)

omit [Fintype I] [Nonempty I] in
theorem compact_face [Finite I] (s : Plane) (c : ℝ) : IsCompact (face point level s c) := by
  have finite : Set.Finite {x | ∃ i, point i = x ∧ level i = inner ℝ (point i) s + c} :=
    (Set.finite_range point).subset (by rintro _ ⟨i, rfl, _⟩; exact ⟨i, rfl⟩)
  exact finite.isCompact_convexHull ℝ

/-- A local maximum in an open slope neighborhood cannot extend an original face domain.
The proof separates an exterior point from the finite contact hull and perturbs the slope. -/
theorem mem_face_of_interior_maximizer {slopes : Set Plane} {s x : Plane}
    (inside : s ∈ interior slopes)
    (maximal : ∀ q ∈ slopes,
      inner ℝ x q - cost point level q ≤ inner ℝ x s - cost point level s) :
    x ∈ face point level s (-cost point level s) := by
  by_contra outside
  obtain ⟨L, a, below, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (compact_face point level s _).isClosed outside
  let d := (InnerProductSpace.toDual ℝ Plane).symm L
  have pairing (y : Plane) : inner ℝ d y = L y := InnerProductSpace.toDual_symm_apply
  let base := cost point level s - inner ℝ x s
  let expression (i : I) (t : ℝ) :=
    inner ℝ (point i) (s + t • d) - level i - inner ℝ x (s + t • d)
  have expand (i : I) (t : ℝ) : expression i t =
      (inner ℝ (point i) s - level i - inner ℝ x s) + t * (L (point i) - L x) := by
    dsimp [expression]
    simp only [inner_add_right, real_inner_smul_right]
    have first : inner ℝ (point i) d = L (point i) :=
      (real_inner_comm _ _).trans (pairing _)
    have last : inner ℝ x d = L x := (real_inner_comm _ _).trans (pairing _)
    rw [first, last]
    ring
  have each (i : I) : ∀ᶠ t in 𝓝[>] (0 : ℝ), expression i t < base := by
    have bound := vertex_le point level s i
    by_cases active : inner ℝ (point i) s - level i = cost point level s
    · have contact : point i ∈ face point level s (-cost point level s) := by
        apply subset_convexHull ℝ _
        exact ⟨i, rfl, by linarith⟩
      have strict : L (point i) < L x := (below _ contact).trans above
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [expand, active]
      dsimp [base]
      nlinarith
    · have strict : expression i 0 < base := by
        rw [expand]
        dsimp [base]
        nlinarith [lt_of_le_of_ne bound active]
      have continuous : Continuous (expression i) := by
        dsimp [expression]
        fun_prop
      have near : ∀ᶠ t in 𝓝 (0 : ℝ), expression i t < base :=
        (isOpen_lt continuous continuous_const).mem_nhds strict
      exact near.filter_mono nhdsWithin_le_nhds
  have all : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, expression i t < base :=
    Filter.eventually_all.mpr each
  have tends : Filter.Tendsto (fun t : ℝ => s + t • d) (𝓝 0) (𝓝 s) := by
    have continuous : Continuous (fun t : ℝ => s + t • d) := by fun_prop
    simpa only [zero_smul, add_zero] using continuous.tendsto 0
  have near0 : ∀ᶠ t in 𝓝 (0 : ℝ), s + t • d ∈ slopes :=
    tends (mem_interior_iff_mem_nhds.mp inside)
  have near : ∀ᶠ t in 𝓝[>] (0 : ℝ), s + t • d ∈ slopes :=
    near0.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, in_slopes, strict⟩ := (near.and all).exists
  obtain ⟨i, equal⟩ := exists_cost_eq point level (s + t • d)
  have max := maximal _ in_slopes
  rw [equal] at max
  have less := strict i
  dsimp [base, expression] at less
  linarith

/-- At an interior surviving supporting slope, the extension's equality domain is exactly
its complete original supporting face, with no new portion added by clipping. -/
theorem clipped_eq_plane_iff {slopes : Set Plane} (compact : IsCompact slopes)
    (nonempty : slopes.Nonempty) {s x : Plane} {c : ℝ}
    (support : ∀ i, inner ℝ (point i) s + c ≤ level i)
    (contact : ∃ i, level i = inner ℝ (point i) s + c)
    (selected : s ∈ interior slopes) :
    (clipped point level slopes compact nonempty).height x = inner ℝ x s + c ↔
      x ∈ face point level s c := by
  have dual := cost_at_support point level support contact
  constructor
  · intro equal
    have member := mem_face_of_interior_maximizer point level selected
      (fun q hq => by
        have lower := (clipped point level slopes compact nonempty).affine_le x hq
        change inner ℝ x q - cost point level q ≤ _ at lower
        rw [equal] at lower
        linarith)
    simpa only [dual, neg_neg] using member
  · exact clipped_preserves_face point level compact nonempty support contact
      (interior_subset selected)

end Unfoldings.FiniteDual
