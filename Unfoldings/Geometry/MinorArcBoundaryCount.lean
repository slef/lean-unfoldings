module

public import Unfoldings.Geometry.MinorArcSupportIntersections
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card
public import Mathlib.Order.SuccPred.ENat

/-! A transverse arc crosses a convex spherical boundary at most twice. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- At most two points of a transverse open minor arc satisfy every support
inequality and attain equality on at least one support. -/
theorem encard_openMinorArc_support_boundary_le {I : Type*} {u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (f : I → Space →ₗ[ℝ] ℝ) (transverse : ∀ i, f i u ≠ 0 ∨ f i v ≠ 0) :
    (openMinorArc u v ∩ {x | (∀ i, 0 ≤ f i x) ∧ ∃ i, f i x = 0}).encard ≤ 2 := by
  classical
  let point (t : ℝ) := NormedSpace.normalize ((1 - t) • u + t • v)
  let params : Set ℝ :=
    {t | t ∈ Set.Ioo 0 1 ∧ (∀ i, 0 ≤ f i (point t)) ∧ ∃ i, f i (point t) = 0}
  have image : openMinorArc u v ∩ {x | (∀ i, 0 ≤ f i x) ∧ ∃ i, f i x = 0} =
      point '' params := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, nonneg, some_zero⟩
      exact ⟨t, ⟨ht, nonneg, some_zero⟩, rfl⟩
    · rintro ⟨t, ⟨ht, nonneg, some_zero⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, nonneg, some_zero⟩
  rw [image]
  apply (Set.encard_image_le point params).trans
  by_contra! many
  have three : (3 : ℕ∞) ≤ params.encard :=
    (ENat.add_one_le_iff (by simp : (2 : ℕ∞) ≠ ⊤)).mpr many
  obtain ⟨T, included, card⟩ := Set.exists_subset_encard_eq three
  have finite : T.Finite := Set.finite_of_encard_eq_coe (show T.encard = (3 : ℕ∞) from card)
  let A := finite.toFinset
  have size : A.card = 3 := by
    rw [← T.ncard_eq_toFinset_card finite, Set.ncard, card]
    rfl
  let order := A.orderEmbOfFin size
  have selected (j : Fin 3) : order j ∈ params :=
    included (finite.mem_toFinset.mp (A.orderEmbOfFin_mem size j))
  obtain ⟨ha, left, _⟩ := selected 0
  obtain ⟨hb, middle, i, zero⟩ := selected 1
  obtain ⟨hc, right, _⟩ := selected 2
  have strict := minorArc_middle_strict_of_crossing_supports hu hv not_antipodal f transverse
    ha hb hc (order.strictMono (by decide : (0 : Fin 3) < 1))
    (order.strictMono (by decide : (1 : Fin 3) < 2)) left middle right
  exact (strict i).ne' zero

end Unfoldings
