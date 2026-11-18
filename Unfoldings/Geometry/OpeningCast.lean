module

public import Unfoldings.Geometry.OpeningBudget
public import Unfoldings.Geometry.PolygonalRayOpening

/-! Length-index transport preserves original opening charges and complete opened banks. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n m : ℕ}

/-- Relabel the same original hinge across an equality of finite path lengths. -/
def Opening.cast (equal : n = m) (event : Opening n) : Opening m :=
  ⟨Fin.cast (congrArg (· + 1) equal) event.hinge, event.angle⟩

/-- Retain the original order and every real opening angle under index transport. -/
def castOpenings (equal : n = m) (events : List (Opening n)) : List (Opening m) :=
  events.map (Opening.cast equal)

@[simp] theorem castOpenings_cons (equal : n = m) (event : Opening n)
    (events : List (Opening n)) :
    castOpenings equal (event :: events) = event.cast equal :: castOpenings equal events := rfl

@[simp] theorem Opening.cast_source (equal : n = m) (angle : ℝ) :
    (Opening.mk 0 angle).cast equal = Opening.mk 0 angle := by
  subst m
  rfl

@[simp] theorem castOpenings_budget (equal : n = m) (events : List (Opening n)) :
    openingBudget (castOpenings equal events) = openingBudget events := by
  simp only [openingBudget, castOpenings, List.map_map, Opening.cast, Function.comp_def]

/-- A transported original history has exactly the same positive events. -/
theorem castOpenings_positive (equal : n = m) (events : List (Opening n))
    (positive : ∀ event ∈ events, 0 < event.angle) :
    ∀ event ∈ castOpenings equal events, 0 < event.angle := by
  intro event member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  exact positive old present

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

variable {n m : ℕ}

/-- Transport only the finite dimension, retaining the entire unbounded bank. -/
def cast (bank : PolygonalRay ℂ n) (equal : n = m) : PolygonalRay ℂ m := equal ▸ bank

@[simp] theorem cast_openings (bank : PolygonalRay ℂ n) (equal : n = m)
    (events : List (PolygonalChain.Opening n)) :
    (bank.openings events).cast equal =
      (bank.cast equal).openings (PolygonalChain.castOpenings equal events) := by
  subst m
  have same : PolygonalChain.castOpenings rfl events = events := by
    exact List.map_id' events
  simp only [same, cast]

@[simp] theorem cast_cast (bank : PolygonalRay ℂ n) (equal : n = m) :
    (bank.cast equal).cast equal.symm = bank := by
  subst m
  rfl

end Unfoldings.PolygonalRay
