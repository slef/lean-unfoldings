module

public import Mathlib.Topology.Homotopy.Lifting

/-! A connected covering homotopic to a homeomorphism has one sheet. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- On a compact domain, finitely many injective pieces provide finite fibers.
A local homeomorphism with this cover is therefore a covering. -/
theorem isCoveringMap_of_compact_injective_cells
    {X Y I : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [Finite I]
    (cells : I → Set X) (cover : ∀ x, ∃ i, x ∈ cells i) {f : X → Y}
    (local_homeomorph : IsLocalHomeomorph f) (on_cell : ∀ i, Set.InjOn f (cells i)) :
    IsCoveringMap f := by
  have closed_map : IsClosedMap f := fun s hs =>
    (hs.isCompact.image local_homeomorph.continuous).isClosed
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply closed_map.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    classical
    choose index member using cover
    have injective : Function.Injective (fun x : f ⁻¹' {y} => index x.val) := by
      intro x z same
      apply Subtype.ext
      apply on_cell (index x.val) (member x.val) _
        (x.property.trans z.property.symm)
      change index x.val = index z.val at same
      rw [same]
      exact member z.val
    let : Finite (f ⁻¹' {y}) := Finite.of_injective _ injective
    exact Set.toFinite _
  · exact local_homeomorph.isLocalHomeomorphOn.mono (Set.subset_univ _)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PreconnectedSpace X] [Nonempty X] {f : X → Y}

/-- Lift the given homotopy starting at the identity. Its endpoint composed
with the inverse homeomorphism is a section. Uniqueness of covering lifts
makes that section a two-sided inverse. -/
def coveringHomeomorphOfHomotopy (covering : IsCoveringMap f) (h : X ≃ₜ Y)
    (H : ContinuousMap.Homotopy ⟨f, covering.continuous⟩ ⟨h, h.continuous⟩) : X ≃ₜ Y := by
  have initial (x : X) : H (0, x) = f ((ContinuousMap.id X) x) := H.apply_zero x
  let lift := covering.liftHomotopy H (ContinuousMap.id X) initial
  let endpoint : C(X, X) :=
    ⟨fun x => lift (1, x), lift.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have endpoint_lifts (x : X) : f (endpoint x) = h x := by
    have equal := congrFun (covering.liftHomotopy_lifts H (ContinuousMap.id X) initial) (1, x)
    exact equal.trans (H.apply_one x)
  let inverse := endpoint ∘ h.symm
  have inverse_continuous : Continuous inverse := endpoint.continuous.comp h.symm.continuous
  have right : Function.RightInverse inverse f := fun y =>
    (endpoint_lifts (h.symm y)).trans (h.apply_symm_apply y)
  let x₀ := inverse (f (Classical.choice (inferInstance : Nonempty X)))
  have fixed : inverse (f x₀) = x₀ :=
    congrArg inverse (right (f (Classical.choice (inferInstance : Nonempty X))))
  have compatible : f ∘ (inverse ∘ f) = f ∘ id :=
    funext (fun x => right (f x))
  have left : inverse ∘ f = id := covering.eq_of_comp_eq
    (inverse_continuous.comp covering.continuous) continuous_id compatible x₀ fixed
  exact {
    toFun := f
    invFun := inverse
    left_inv := fun x => congrFun left x
    right_inv := right
    continuous_toFun := covering.continuous
    continuous_invFun := inverse_continuous }

end Unfoldings
