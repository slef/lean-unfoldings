module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metric and exactness when no seams are retained

Each cell keeps its original extended metric and distinct cells are infinitely
far apart. With separated input cells, no distinct tagged points are identified.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v)

section Pseudo

variable [∀ i, PseudoEMetricSpace (E i)]

@[simp] theorem faceCost_self (x : Total E) : faceCost E x x = 0 := by
  obtain ⟨i, x⟩ := x
  simp [faceCost]

theorem faceCost_triangle (x y z : Total E) :
    faceCost E x z ≤ faceCost E x y + faceCost E y z := by
  classical
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  obtain ⟨k, z⟩ := z
  by_cases ij : i = j
  · subst j
    by_cases ik : i = k
    · subst k
      simpa [faceCost] using edist_triangle x y z
    · simp [faceCost, ik]
  · simp [faceCost, ij]

/-- With no seams, route optimization cannot improve on a single within-cell step. -/
theorem distance_empty (x y : Total E) :
    Route.distance (stepCost E (fun _ _ => False)) x y = faceCost E x y := by
  apply le_antisymm
  · simpa [stepCost] using Route.distance_le_cost (stepCost E (fun _ _ => False)) x y
  · exact Route.le_distance (stepCost E (fun _ _ => False)) (faceCost E)
      (faceCost_self E) (faceCost_triangle E) (by intro a b; simp [stepCost]) x y

@[simp] theorem edist_of_empty (i : ι) (x y : E i) :
    edist (of E (fun _ _ => False) i x) (of E (fun _ _ => False) i y) = edist x y := by
  change Route.distance (stepCost E (fun _ _ => False)) ⟨i, x⟩ ⟨i, y⟩ = edist x y
  simp [distance_empty, faceCost]

theorem edist_of_empty_of_ne {i j : ι} (different : i ≠ j) (x : E i) (y : E j) :
    edist (of E (fun _ _ => False) i x) (of E (fun _ _ => False) j y) = ⊤ := by
  change Route.distance (stepCost E (fun _ _ => False)) ⟨i, x⟩ ⟨j, y⟩ = ⊤
  simp [distance_empty, faceCost, different]

/-- No uncut transitions means every original cell embeds isometrically. -/
theorem of_empty_isometry (i : ι) : Isometry (of E (fun _ _ => False) i) :=
  edist_of_empty E i

end Pseudo

/-- For separated input cells the completely cut realization makes no identifications. -/
theorem exact_empty [∀ i, EMetricSpace (E i)] : Exact E (fun _ _ => False) := by
  classical
  intro a b equal
  have zero := edist_eq_zero.mpr equal
  rw [edist_point, distance_empty] at zero
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  by_cases ij : i = j
  · subst j
    have ab : a = b := edist_eq_zero.mp (by simpa [faceCost] using zero)
    subst b
    exact Relation.EqvGen.refl _
  · simp [faceCost, ij] at zero

end Unfoldings.MetricGluing
