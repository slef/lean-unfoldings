module

public import Unfoldings.Geometry.ClippedRadialTails
public import Mathlib.Data.Fintype.Lattice

/-! A finite radial tail family reduces to pairwise disjoint whole segment components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p r : E} (T : RadialClipTail S q p) (U : RadialClipTail S q r)

theorem carrier_subset_of_tip_eq (same : T.tip = U.tip) (ordered : U.start ≤ T.start) :
    T.carrier ⊆ U.carrier := by
  rw [T.carrier_eq_image, U.carrier_eq_image, same]
  exact Set.image_mono (Set.Icc_subset_Icc_left ordered)

end Unfoldings.RadialClipTail

namespace Unfoldings.RadialTailFamily

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  {S : Set E} {q : E} {seed : I → E} (tail : ∀ i, RadialClipTail S q (seed i))

abbrev Component := Set.range (fun i => (tail i).tip)

instance finiteComponent : Finite (Component tail) :=
  (Set.finite_range (fun i => (tail i).tip)).to_subtype

theorem exists_component_seed (c : Component tail) :
    ∃ i, (tail i).tip = c.val ∧ ∀ j, (tail j).tip = c.val → (tail i).start ≤ (tail j).start := by
  classical
  let Active := {i // (tail i).tip = c.val}
  have nonempty : Nonempty Active := by
    obtain ⟨i, equal⟩ := c.property
    exact ⟨i, equal⟩
  let := nonempty
  obtain ⟨i, minimal⟩ := Finite.exists_min (fun i : Active => (tail i.val).start)
  exact ⟨i.val, i.property, fun j same => minimal ⟨j, same⟩⟩

def componentSeed (c : Component tail) : I := (exists_component_seed tail c).choose

def componentTail (c : Component tail) : RadialClipTail S q (seed (componentSeed tail c)) :=
  tail (componentSeed tail c)

theorem component_tip (c : Component tail) : (componentTail tail c).tip = c.val :=
  (exists_component_seed tail c).choose_spec.1

theorem component_minimal (c : Component tail) (i : I) (same : (tail i).tip = c.val) :
    (componentTail tail c).start ≤ (tail i).start :=
  (exists_component_seed tail c).choose_spec.2 i same

/-- Every supplied tail belongs to its unique rim-labeled whole segment component. -/
theorem tail_subset_component (i : I) :
    (tail i).carrier ⊆ (componentTail tail ⟨(tail i).tip, i, rfl⟩).carrier :=
  (tail i).carrier_subset_of_tip_eq _
    (component_tip tail ⟨(tail i).tip, i, rfl⟩).symm
    (component_minimal tail ⟨(tail i).tip, i, rfl⟩ i rfl)

/-- Distinct rim labels give disjoint entire components, including all endpoints. -/
theorem components_disjoint (convex : Convex ℝ S) (origin : q ∈ interior S) :
    Pairwise (fun c d : Component tail =>
      Disjoint (componentTail tail c).carrier (componentTail tail d).carrier) := by
  intro c d different
  apply Set.disjoint_left.mpr
  intro x first last
  apply different
  apply Subtype.ext
  exact (component_tip tail c).symm.trans
    (((componentTail tail c).tip_eq_of_intersection convex origin
      (componentTail tail d) first last).trans (component_tip tail d))

/-- Removing nested duplicates preserves the entire actual cut set. -/
theorem union_components : (⋃ c : Component tail, (componentTail tail c).carrier) =
    ⋃ i, (tail i).carrier := by
  apply Set.Subset.antisymm
  · intro x member
    obtain ⟨c, member⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨componentSeed tail c, member⟩
  · intro x member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨⟨(tail i).tip, i, rfl⟩, tail_subset_component tail i member⟩

theorem seeds_covered (i : I) : seed i ∈ ⋃ c : Component tail, (componentTail tail c).carrier := by
  rw [union_components]
  exact Set.mem_iUnion.mpr ⟨i, (tail i).seed_mem⟩

end Unfoldings.RadialTailFamily
