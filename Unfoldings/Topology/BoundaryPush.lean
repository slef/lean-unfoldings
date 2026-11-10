module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Compactness.Compact

/-!
# Combining local boundary pushes

An inward push preserves the complement of a boundary and either fixes each
boundary point or moves it off the boundary. Finite compositions accumulate
all the moved boundary patches. Compactness therefore turns local inward
pushes into a single embedding whose whole image misses the boundary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [TopologicalSpace X] (B : Set X)

structure BoundaryPush where
  map : C(X, X)
  injective : Function.Injective map
  interior : Set.MapsTo map Bᶜ Bᶜ
  boundary : ∀ x ∈ B, map x = x ∨ map x ∉ B

namespace BoundaryPush

variable {B}

def identity : BoundaryPush B where
  map := ContinuousMap.id X
  injective := Function.injective_id
  interior := fun _ h => h
  boundary := fun _ _ => Or.inl rfl

/-- Apply `f` first and then `g`; every patch moved by either remains moved. -/
def comp (g f : BoundaryPush B) : BoundaryPush B where
  map := g.map.comp f.map
  injective := g.injective.comp f.injective
  interior := g.interior.comp f.interior
  boundary x hx := by
    rcases f.boundary x hx with fixed | moved
    · change g.map (f.map x) = x ∨ g.map (f.map x) ∉ B
      rw [fixed]
      exact g.boundary x hx
    · exact Or.inr (g.interior moved)

def moved (f : BoundaryPush B) : Set X := {x | x ∈ B ∧ f.map x ∉ B}

theorem moved_subset_comp_left (g f : BoundaryPush B) : g.moved ⊆ (g.comp f).moved := by
  rintro x ⟨boundary, moved⟩
  refine ⟨boundary, ?_⟩
  rcases f.boundary x boundary with fixed | earlier
  · change g.map (f.map x) ∉ B
    rwa [fixed]
  · exact g.interior earlier

theorem moved_subset_comp_right (g f : BoundaryPush B) : f.moved ⊆ (g.comp f).moved := by
  rintro x ⟨boundary, moved⟩
  exact ⟨boundary, g.interior moved⟩

theorem exists_moves_finite_family {ι : Type*} (pushes : ι → BoundaryPush B)
    (indices : Finset ι) :
    ∃ f : BoundaryPush B, ∀ i ∈ indices, (pushes i).moved ⊆ f.moved := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨identity, by simp⟩
  | @insert i indices fresh ih =>
    obtain ⟨f, covers⟩ := ih
    refine ⟨(pushes i).comp f, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | member
    · exact moved_subset_comp_left _ _
    · exact (covers j member).trans (moved_subset_comp_right _ _)

/-- Compactly many local inward pushes suffice to move the whole boundary. -/
theorem exists_misses_boundary (compact : IsCompact B)
    (local_push : ∀ x ∈ B, ∃ f : BoundaryPush B,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ B ⊆ f.moved) :
    ∃ f : BoundaryPush B, ∀ x, f.map x ∉ B := by
  classical
  choose pushes U open_U contains moves using (fun p : B => local_push p.val p.property)
  have cover : B ⊆ ⋃ p : B, U p := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, contains ⟨x, hx⟩⟩
  obtain ⟨indices, covers⟩ := compact.elim_finite_subcover U open_U cover
  obtain ⟨f, moves_all⟩ := exists_moves_finite_family pushes indices
  refine ⟨f, ?_⟩
  intro x
  by_cases boundary : x ∈ B
  · obtain ⟨p, member, near⟩ := Set.mem_iUnion₂.mp (covers boundary)
    exact (moves_all p member (moves p ⟨near, boundary⟩)).2
  · exact f.interior boundary

/-- On a compact Hausdorff space the resulting map is a closed embedding. -/
theorem exists_embedding_misses_boundary [CompactSpace X] [T2Space X]
    (compact : IsCompact B)
    (local_push : ∀ x ∈ B, ∃ f : BoundaryPush B,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ B ⊆ f.moved) :
    ∃ f : C(X, X), Topology.IsClosedEmbedding f ∧ Set.range f ⊆ Bᶜ := by
  obtain ⟨f, misses⟩ := exists_misses_boundary compact local_push
  exact ⟨f.map, f.map.continuous.isClosedEmbedding f.injective,
    by rintro _ ⟨x, rfl⟩; exact misses x⟩

/-- A push supported inside a chart and moving a neighborhood of its center. -/
structure Local (U : Set X) (x : X) where
  push : BoundaryPush B
  support : Set X
  compact_support : IsCompact support
  support_subset : support ⊆ U
  invariant_support : Set.MapsTo push.map support support
  fixed_outside : ∀ y, y ∉ support → push.map y = y
  neighborhood : Set X
  open_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  neighborhood_subset : neighborhood ⊆ U
  moves_neighborhood : neighborhood ∩ B ⊆ push.moved

/-- Restrict a push to an invariant chart domain. -/
def restrict (f : BoundaryPush B) (U : Set X) (invariant : Set.MapsTo f.map U U) :
    BoundaryPush (Subtype.val ⁻¹' B : Set U) where
  map := ⟨fun x => ⟨f.map x.val, invariant x.property⟩,
    (f.map.continuous.comp continuous_subtype_val).subtype_mk _⟩
  injective := by
    intro x y equal
    exact Subtype.ext (f.injective (congrArg Subtype.val equal))
  interior := fun _ hx => f.interior hx
  boundary := by
    intro x hx
    rcases f.boundary x.val hx with fixed | moved
    · exact Or.inl (Subtype.ext fixed)
    · exact Or.inr moved

/-- Change coordinates while preserving the distinguished boundary. -/
def transport {Y : Type*} [TopologicalSpace Y] (D : Set Y) (e : X ≃ₜ Y)
    (boundary : ∀ x, x ∈ B ↔ e x ∈ D) (f : BoundaryPush B) : BoundaryPush D where
  map := ⟨fun y => e (f.map (e.symm y)), by fun_prop⟩
  injective := e.injective.comp (f.injective.comp e.symm.injective)
  interior := by
    intro y hy
    change y ∉ D at hy
    have original : e.symm y ∉ B := by
      intro inside
      exact hy (by simpa only [Homeomorph.apply_symm_apply] using (boundary _).mp inside)
    exact fun inside => f.interior original ((boundary _).mpr inside)
  boundary := by
    intro y hy
    have original : e.symm y ∈ B := (boundary _).mpr (by
      simpa only [Homeomorph.apply_symm_apply] using hy)
    rcases f.boundary (e.symm y) original with fixed | moved
    · left
      change e (f.map (e.symm y)) = y
      rw [fixed, Homeomorph.apply_symm_apply]
    · right
      exact fun inside => moved ((boundary _).mpr inside)

end BoundaryPush

end Unfoldings
