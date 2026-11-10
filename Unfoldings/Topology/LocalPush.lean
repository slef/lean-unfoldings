module

public import Unfoldings.Topology.BoundaryPush
public import Mathlib.Topology.ContinuousOn

/-!
# Extending local inward pushes by the identity

A continuous injective self-map of an open chart extends to the ambient space
when it is fixed off a closed subset contained in that chart. Boundary pushes
retain their interior-preservation and fixed-or-inward properties under this
extension. No ambient manifold or global collar is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} (U : Set X)

def extendLocalByIdentity (f : U → U) (x : X) : X := by
  classical
  exact if h : x ∈ U then (f ⟨x, h⟩).val else x

@[simp] theorem extendLocalByIdentity_apply (f : U → U) (x : U) :
    extendLocalByIdentity U f x.val = (f x).val := by
  classical
  simp only [extendLocalByIdentity, dite_eq_left x.property]

@[simp] theorem extendLocalByIdentity_of_mem (f : U → U) (x : X) (inside : x ∈ U) :
    extendLocalByIdentity U f x = (f ⟨x, inside⟩).val := by
  classical
  simp only [extendLocalByIdentity, dite_eq_left inside]

theorem extendLocalByIdentity_fixed (f : U → U) {x : X} (outside : x ∉ U) :
    extendLocalByIdentity U f x = x := by
  classical
  simp only [extendLocalByIdentity, dite_eq_right outside]

theorem extendLocalByIdentity_mem_iff (f : U → U) (x : X) :
    extendLocalByIdentity U f x ∈ U ↔ x ∈ U := by
  classical
  by_cases inside : x ∈ U
  · simp only [extendLocalByIdentity, dite_eq_left inside]
    exact iff_of_true (f ⟨x, inside⟩).property inside
  · rw [extendLocalByIdentity_fixed U f inside]

theorem extendLocalByIdentity_injective (f : U → U) (injective : Function.Injective f) :
    Function.Injective (extendLocalByIdentity U f) := by
  intro x y equal
  have membership : x ∈ U ↔ y ∈ U := by
    rw [← extendLocalByIdentity_mem_iff U f x, equal, extendLocalByIdentity_mem_iff U f y]
  by_cases inside : x ∈ U
  · have other := membership.mp inside
    have values : f ⟨x, inside⟩ = f ⟨y, other⟩ := by
      apply Subtype.ext
      simpa only [← extendLocalByIdentity_apply] using equal
    exact congrArg Subtype.val (injective values)
  · have other := mt membership.mpr inside
    simpa only [extendLocalByIdentity_fixed U f inside,
      extendLocalByIdentity_fixed U f other] using equal

variable [TopologicalSpace X]

theorem continuous_extendLocalByIdentity (open_U : IsOpen U) (f : U → U)
    (continuous_f : Continuous f) (K : Set X) (closed_K : IsClosed K)
    (contained : K ⊆ U) (fixed : ∀ x : U, x.val ∉ K → f x = x) :
    Continuous (extendLocalByIdentity U f) := by
  have continuous_inside : ContinuousOn (extendLocalByIdentity U f) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : U => extendLocalByIdentity U f x.val)
    simpa only [extendLocalByIdentity_apply, Function.comp_def] using
      continuous_subtype_val.comp continuous_f
  have fixed_outside (x : X) (outside : x ∉ K) : extendLocalByIdentity U f x = x := by
    by_cases inside : x ∈ U
    · have value := congrArg Subtype.val (fixed ⟨x, inside⟩ outside)
      simpa only [extendLocalByIdentity_of_mem U f x inside] using value
    · exact extendLocalByIdentity_fixed U f inside
  have continuous_outside : ContinuousOn (extendLocalByIdentity U f) Kᶜ :=
    continuousOn_id.congr (fun x hx => fixed_outside x hx)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases inside : x ∈ U
  · exact continuous_inside.continuousAt (open_U.mem_nhds inside)
  · exact continuous_outside.continuousAt
      (closed_K.isOpen_compl.mem_nhds (mt (fun member => contained member) inside))

namespace BoundaryPush

variable {U} (B : Set X)

/-- Extend a push in an open chart without changing points outside its closed support. -/
def ofLocal (open_U : IsOpen U) (f : BoundaryPush (Subtype.val ⁻¹' B : Set U))
    (K : Set X) (closed_K : IsClosed K) (contained : K ⊆ U)
    (fixed : ∀ x : U, x.val ∉ K → f.map x = x) : BoundaryPush B where
  map := ⟨extendLocalByIdentity U f.map,
    continuous_extendLocalByIdentity U open_U f.map f.map.continuous K closed_K contained fixed⟩
  injective := extendLocalByIdentity_injective U f.map f.injective
  interior := by
    intro x hx
    change x ∉ B at hx
    by_cases inside : x ∈ U
    · change extendLocalByIdentity U f.map x ∉ B
      rw [show x = (⟨x, inside⟩ : U).val from rfl, extendLocalByIdentity_apply]
      exact f.interior hx
    · change extendLocalByIdentity U f.map x ∉ B
      simpa only [extendLocalByIdentity_fixed U f.map inside] using hx
  boundary := by
    intro x hx
    by_cases inside : x ∈ U
    · rcases f.boundary ⟨x, inside⟩ hx with same | moved
      · left
        change extendLocalByIdentity U f.map x = x
        simpa only [extendLocalByIdentity_of_mem U f.map x inside] using
          congrArg Subtype.val same
      · right
        change (f.map ⟨x, inside⟩).val ∉ B at moved
        change extendLocalByIdentity U f.map x ∉ B
        simpa only [extendLocalByIdentity_of_mem U f.map x inside] using moved
    · exact Or.inl (extendLocalByIdentity_fixed U f.map inside)

end BoundaryPush

end Unfoldings
