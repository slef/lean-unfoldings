module

public import Unfoldings.Geometry.SpatialEnvelopeWindowCompact
public import Unfoldings.Geometry.SpatialGraphPartition

/-! Selected whole-roof window cells cover the entire closed polygonal window exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] {J : Type*}
  (equations : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, equations j ≠ 0) (signs : A → J → Bool)
  (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
    0 ≤ AffineArrangement.signed (equations j) (signs a j) z)
  (full : (interior {z | ∀ j, 0 ≤ equations j z}).Nonempty)

include proper aligned full in
/-- The actual selected cells cover every window point, including boundary points. -/
theorem windowFootprint_cover : {z | ∀ j, 0 ≤ equations j z} =
    ⋃ a : {a // WindowSelected signs a}, P.footprint a.val := by
  let window : Set Plane := {z | ∀ j, 0 ≤ equations j z}
  let chosen := ⋃ a : {a // WindowSelected signs a}, P.footprint a.val
  have window_eq : window = ⋂ j, {z | 0 ≤ equations j z} := by
    ext z
    simp only [window, Set.mem_iInter, Set.mem_ofPred_eq]
  have convex_window : Convex ℝ window := by
    rw [window_eq]
    exact convex_iInter (fun j => (convex_Ici (0 : ℝ)).affine_preimage (equations j))
  have closed_window : IsClosed window := by
    rw [window_eq]
    exact isClosed_iInter (fun j => isClosed_le continuous_const
      (equations j).continuous_of_finiteDimensional)
  have closed_chosen : IsClosed chosen :=
    isClosed_iUnion_of_finite (fun a => P.closed a.val)
  have interior_covered : interior window ⊆ chosen := by
    intro x inside
    have positive (j : J) : 0 < equations j x := by
      have lower : 0 ≤ equations j x := (interior_subset inside) j
      have nonzero : equations j x ≠ 0 := fun zero =>
        not_mem_interior_of_affine_lower_bound (s := window) (equations j) (proper j)
          (fun z hz => hz j) zero inside
      exact lt_of_le_of_ne lower nonzero.symm
    have covered : x ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ x
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp covered
    have selected : WindowSelected signs a := by
      intro j
      have bound := aligned a x member j
      cases value : signs a j
      · have nonpositive : equations j x ≤ 0 := by
          simpa only [AffineArrangement.signed_apply, value, Bool.false_eq_true,
            ↓reduceIte, neg_nonneg] using bound
        exact False.elim ((not_lt_of_ge nonpositive) (positive j))
      · rfl
    exact Set.mem_iUnion.mpr ⟨⟨a, selected⟩, member⟩
  apply Set.Subset.antisymm
  · have regular : closure (interior window) = window :=
      (convex_window.closure_interior_eq_closure_of_nonempty_interior full).trans
        closed_window.closure_eq
    exact regular.symm.le.trans (closure_minimal interior_covered closed_chosen)
  · exact Set.iUnion_subset (fun a =>
      P.windowSelected_footprint_subset equations signs aligned a.val a.property)

/-- The actual complete window is a graph patch in its original rigid support planes. -/
def windowGraphPartition : SpatialGraphPartition (height family)
    {z | ∀ j, 0 ≤ equations j z} {a // WindowSelected signs a} where
  footprint a := P.footprint a.val
  plane a := family (P.support a.val)
  closed a := P.closed a.val
  convex a := P.convex a.val
  full a := P.full a.val
  disjoint a b different := P.disjoint a.val b.val (fun equal => different (Subtype.ext equal))
  cover := P.windowFootprint_cover equations proper signs aligned full
  active a p member := P.active a.val p member

/-- The graph-patch cut is exactly the already constructed actual window cut. -/
def windowGraphCutEquiv (cuts : Set Plane) : P.WindowCut signs cuts ≃ᵢ
    (P.windowGraphPartition equations proper signs aligned full).Cut cuts := IsometryEquiv.refl _

/-- Every original spatial roof point is unchanged by the window graph-patch presentation. -/
theorem fold_windowGraphCutEquiv (cuts : Set Plane) (x : P.WindowCut signs cuts) :
    (P.windowGraphPartition equations proper signs aligned full).fold cuts
      (P.windowGraphCutEquiv equations proper signs aligned full cuts x) =
        (P.restoreCut cuts (P.windowCutMap signs cuts x)).val :=
  (P.restoreCut_windowCutMap signs cuts x).symm

end Unfoldings.SpatialEnvelope.WholePartition
