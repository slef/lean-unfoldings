module

public import Unfoldings.FewestNets.CheckedPlane
public import Unfoldings.FewestNets.CheckedEnclosureReuse

/-! Validate a table of tangent-chart enclosures once and reuse it in all side tests. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- Integer interval data for a realized normalized mesh chart. -/
structure RoutingChartCache (D S : ℕ) where
  corner : Fin S → Fin 2 → FixedPointInterval D
  normal : Fin S → Fin 2 → FixedPointInterval D
  offset : Fin S → FixedPointInterval D

namespace RoutingChartCache

variable {D S : ℕ} (cache : RoutingChartCache D S)
  {corner normal : Fin S → Plane} {offset : Fin S → ℝ}
  (cp : ∀ k, CheckedPlane D (corner k)) (cn : ∀ k, CheckedPlane D (normal k))
  (co : ∀ k, CheckedReal D (offset k))

/-- Check that the cache contains the spatially computed enclosures. -/
def check : Bool :=
  (List.finRange S).all fun k =>
    (List.finRange 2).all (fun j => (cp k j).insideBounds (cache.corner k j)) &&
    (List.finRange 2).all (fun j => (cn k j).insideBounds (cache.normal k j)) &&
    (co k).insideBounds (cache.offset k)

/-- Each side of a passed cache has all five validated enclosures. -/
theorem checked_at (passed : cache.check cp cn co = true) (k : Fin S) :
    ((List.finRange 2).all (fun j => (cp k j).insideBounds (cache.corner k j)) = true ∧
      (List.finRange 2).all (fun j => (cn k j).insideBounds (cache.normal k j)) = true) ∧
    (co k).insideBounds (cache.offset k) = true := by
  have h := List.all_eq_true.mp passed k (List.mem_finRange k)
  simpa only [Bool.and_eq_true] using h

def checkedCorner (passed : cache.check cp cn co = true) (k : Fin S) :
    CheckedPlane D (corner k) :=
  fun j => (cp k j).withWiderBounds (cache.corner k j)
    (List.all_eq_true.mp (cache.checked_at cp cn co passed k).1.1 j (List.mem_finRange j))

def checkedNormal (passed : cache.check cp cn co = true) (k : Fin S) :
    CheckedPlane D (normal k) :=
  fun j => (cn k j).withWiderBounds (cache.normal k j)
    (List.all_eq_true.mp (cache.checked_at cp cn co passed k).1.2 j (List.mem_finRange j))

def checkedOffset (passed : cache.check cp cn co = true) (k : Fin S) :
    CheckedReal D (offset k) :=
  (co k).withWiderBounds (cache.offset k) (cache.checked_at cp cn co passed k).2

end RoutingChartCache
end Unfoldings.FewestNets
