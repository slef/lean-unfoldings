module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-! A local homeomorphism is a covering when finitely many complete isometric cells cover it. -/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v w z

variable {I : Type u} [Finite I] {X : Type v} [TopologicalSpace X]
  {Y : Type w} [EMetricSpace Y] (E : I → Type z) [∀ i, EMetricSpace (E i)]
  [∀ i, CompleteSpace (E i)] (cell : ∀ i, E i → X)
  (continuous_cell : ∀ i, Continuous (cell i))
  (cover : ∀ x : X, ∃ i, ∃ p : E i, cell i p = x)
  (f : X → Y) (isometric : ∀ i, Isometry (f ∘ cell i))

include continuous_cell cover isometric in
/-- Complete cell isometries and a finite cell cover make the whole map closed. -/
theorem isClosedMap_of_finite_complete_cells : IsClosedMap f := by
  intro A closed_A
  have equal : f '' A = ⋃ i, (f ∘ cell i) '' (cell i ⁻¹' A) := by
    ext y
    constructor
    · rintro ⟨x, member, rfl⟩
      obtain ⟨i, p, rfl⟩ := cover x
      exact Set.mem_iUnion.mpr ⟨i, p, member, rfl⟩
    · intro member
      obtain ⟨i, p, in_A, rfl⟩ := Set.mem_iUnion.mp member
      exact ⟨cell i p, in_A, rfl⟩
  rw [equal]
  exact isClosed_iUnion_of_finite (fun i =>
    (isometric i).isClosedEmbedding.isClosedMap _ (closed_A.preimage (continuous_cell i)))

omit [TopologicalSpace X] [∀ i, CompleteSpace (E i)] in
include cover isometric in
/-- Each cell contains at most one point of a fiber. -/
theorem finite_fibers_of_finite_isometric_cells (y : Y) : (f ⁻¹' {y}).Finite := by
  classical
  choose index point at_point using cover
  have injective : Function.Injective (fun x : f ⁻¹' {y} => index x.val) := by
    intro x z same
    apply Subtype.ext
    have same_image : f x.val = f z.val := x.property.trans z.property.symm
    have injective_on (i : I) : Set.InjOn f (Set.range (cell i)) := by
      rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ equal
      exact congrArg (cell i) ((isometric i).injective equal)
    apply injective_on (index x.val) ⟨point x.val, at_point x.val⟩ _ same_image
    change index x.val = index z.val at same
    rw [same]
    exact ⟨point z.val, at_point z.val⟩
  let := Finite.of_injective _ injective
  exact Set.toFinite _

include continuous_cell cover isometric in
/-- This covering conclusion is derived from actual cell isometries, not assumed. -/
theorem isCoveringMap_of_finite_complete_cells [T2Space X]
    (local_homeomorph : IsLocalHomeomorph f) : IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  have closed_map := isClosedMap_of_finite_complete_cells E cell continuous_cell cover f isometric
  apply closed_map.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    exact finite_fibers_of_finite_isometric_cells E cell cover f isometric y
  · exact local_homeomorph.isLocalHomeomorphOn.mono (Set.subset_univ _)

end Unfoldings

namespace Unfoldings

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PreconnectedSpace X] [Nonempty X] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
  {f : X → Y}

/-- A connected covering of a simply connected base has one sheet. -/
def coveringHomeomorphOfSimplyConnected (covering : IsCoveringMap f) : X ≃ₜ Y := by
  let root : X := Classical.choice inferInstance
  let result := covering.existsUnique_continuousMap_lifts (ContinuousMap.id Y)
    (f root) root rfl
  let inverse := result.choose
  have initial : inverse (f root) = root := result.choose_spec.1.1
  have lifts : f ∘ inverse = ContinuousMap.id Y := result.choose_spec.1.2
  have left_inverse : Function.LeftInverse inverse f := by
    have same : inverse ∘ f = id := covering.eq_of_comp_eq
      (inverse.continuous.comp covering.continuous) continuous_id
      (by funext x; exact congrFun lifts (f x)) root initial
    exact fun x => congrFun same x
  exact {
    toFun := f
    invFun := inverse
    left_inv := left_inverse
    right_inv := fun y => congrFun lifts y
    continuous_toFun := covering.continuous
    continuous_invFun := inverse.continuous }

end Unfoldings
