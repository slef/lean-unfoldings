module

public import Unfoldings.Topology.SelectedForest
public import Mathlib.Logic.Relation

/-! Compatible parent choices from the three available exterior directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Relation

variable {V : Type*}

/-- Two possible upward links at each interior vertex. At a boundary vertex,
a compatible exit may be available for one or both choices. -/
structure ThreeExitChoices (V : Type*) where
  boundary : Set V
  height : V → ℝ
  eastParent : V → V
  westParent : V → V
  east_up : ∀ v ∉ boundary, height v < height (eastParent v)
  west_up : ∀ v ∉ boundary, height v < height (westParent v)
  eastAvailable : V → Prop
  westAvailable : V → Prop
  available : ∀ v ∈ boundary, eastAvailable v ∨ westAvailable v

namespace ThreeExitChoices

variable (R : ThreeExitChoices V)

/-- East choices point forward. West choices point backward. -/
def constraint (v w : V) : Prop :=
  (v ∉ R.boundary ∧ R.eastParent v = w) ∨ (w ∉ R.boundary ∧ R.westParent w = v)

def forcedEast (v : V) : Prop := v ∈ R.boundary ∧ ¬ R.westAvailable v

def forcedWest (v : V) : Prop := v ∈ R.boundary ∧ ¬ R.eastAvailable v

/-- Choose the east option precisely on the closure of the forced east roots. -/
def choosesEast (v : V) : Prop :=
  ∃ r, R.forcedEast r ∧ ReflTransGen R.constraint r v

theorem choosesEast_of_forcedEast {v : V} (forced : R.forcedEast v) : R.choosesEast v :=
  ⟨v, forced, .refl⟩

theorem choosesEast_of_constraint {v w : V} (step : R.constraint v w)
    (east : R.choosesEast v) : R.choosesEast w := by
  obtain ⟨r, forced, path⟩ := east
  exact ⟨r, forced, path.tail step⟩

theorem eastAvailable_of_choosesEast
    (no_path : ∀ r s, R.forcedEast r → R.forcedWest s → ¬ ReflTransGen R.constraint r s)
    {v : V} (boundary : v ∈ R.boundary) (east : R.choosesEast v) : R.eastAvailable v := by
  by_contra unavailable
  obtain ⟨r, forced, path⟩ := east
  exact no_path r v forced ⟨boundary, unavailable⟩ path

theorem westAvailable_of_not_choosesEast {v : V} (boundary : v ∈ R.boundary)
    (west : ¬ R.choosesEast v) : R.westAvailable v := by
  by_contra unavailable
  exact west (R.choosesEast_of_forcedEast ⟨boundary, unavailable⟩)

open Classical in
/-- Orient the selected edges toward the boundary using the north coordinate. -/
def parents : AscendingParents V where
  roots := R.boundary
  parent v :=
    if v ∈ R.boundary then v else if R.choosesEast v then R.eastParent v else R.westParent v
  height := R.height
  fixed_root v h := ite_eq_left h
  ascending v h := by
    simp only [ite_eq_right h]
    split
    · exact R.east_up v h
    · exact R.west_up v h

open Classical in
theorem parent_eq (v : V) (interior : v ∉ R.boundary) :
    R.parents.parent v = if R.choosesEast v then R.eastParent v else R.westParent v := by
  simp [parents, interior]

theorem choosesEast_parent_iff (v : V) :
    R.choosesEast (R.parents.parent v) ↔ R.choosesEast v := by
  classical
  by_cases boundary : v ∈ R.boundary
  · rw [R.parents.fixed_root v boundary]
  rw [R.parent_eq v boundary]
  by_cases east : R.choosesEast v
  · rw [ite_eq_left east]
    exact ⟨fun _ => east, R.choosesEast_of_constraint (Or.inl ⟨boundary, rfl⟩)⟩
  · rw [ite_eq_right east]
    exact ⟨fun conflict => (east (R.choosesEast_of_constraint
      (Or.inr ⟨boundary, rfl⟩) conflict)).elim, fun conflict => (east conflict).elim⟩

/-- All original-edge links in a parent history make the same direction choice. -/
theorem choosesEast_ancestor_iff {v w : V} (ancestor : R.parents.Ancestor v w) :
    R.choosesEast w ↔ R.choosesEast v := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', R.choosesEast_parent_iff, ih]

open Classical in
/-- Keep the names of the input edges selected by the two direction choices. -/
def edgeSelection {E : Type*} (G : Graph V E)
    (eastEdge westEdge : {v : V // v ∉ R.boundary} → E)
    (eastLink : ∀ v, G.IsLink (eastEdge v) v.val (R.eastParent v.val))
    (westLink : ∀ v, G.IsLink (westEdge v) v.val (R.westParent v.val)) :
    R.parents.EdgeSelection G where
  edge v := if R.choosesEast v.val then eastEdge v else westEdge v
  link v := by
    rw [R.parent_eq v.val v.property]
    by_cases east : R.choosesEast v.val
    · simpa only [ite_eq_left east] using eastLink v
    · simpa only [ite_eq_right east] using westLink v

end ThreeExitChoices

end Unfoldings.FewestNets
