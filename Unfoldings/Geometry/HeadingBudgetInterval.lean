module

public import Unfoldings.Geometry.LocalHeadingBudget
public import Unfoldings.Geometry.ChainPolarVariation

/-! Exact local polar windows in consecutive physical subchains. -/

@[expose] public section

namespace Unfoldings

variable {N : ℕ}

/-- A consecutive restriction has exactly the original strict interior variation. -/
theorem interiorVariation_interval (variation : Fin N → ℝ) (first length : ℕ)
    (fits : first + length ≤ N) (a b : Fin length) :
    interiorVariation (fun i : Fin length => variation ⟨first + i.val, by omega⟩) a b =
      interiorVariation variation ⟨first + a.val, by omega⟩ ⟨first + b.val, by omega⟩ := by
  classical
  unfold interiorVariation
  apply Finset.sum_bij (fun k _ => (⟨first + k.val, by omega⟩ : Fin N))
  · intro k member
    have bounds := (Finset.mem_filter.mp member).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by constructor <;> change first + _ < first + _ <;> omega⟩
  · intro i _ j _ same
    apply Fin.ext
    have equal := congrArg Fin.val same
    dsimp only at equal
    omega
  · intro k member
    have bounds := (Finset.mem_filter.mp member).2
    have low : first ≤ k.val := by
      have lower : first + a.val < k.val := bounds.1
      omega
    let j : Fin length := ⟨k.val - first, by
      have upper : k.val < first + b.val := bounds.2
      omega⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change a.val < k.val - first ∧ k.val - first < b.val
      have lower : first + a.val < k.val := bounds.1
      have upper : k.val < first + b.val := bounds.2
      omega
    · apply Fin.ext
      change first + (k.val - first) = k.val
      omega
  · intro k _
    rfl

namespace PolygonalChain

variable (P : PolygonalChain ℂ N) (source : ℂ)

/-- Each actual subchain link has its original polar variation. -/
theorem polarVariation_interval (first length : ℕ) (fits : first + length ≤ N)
    (i : Fin length) :
    (P.interval first length fits).polarVariation source i =
      P.polarVariation source ⟨first + i.val, by omega⟩ := by
  unfold polarVariation
  have endpoint : (P.interval first length fits).vertex i.succ =
      P.vertex (⟨first + i.val, by omega⟩ : Fin N).succ := by
    apply congrArg P.vertex
    apply Fin.ext
    change first + (i.val + 1) = first + i.val + 1
    omega
  rw [endpoint]
  rfl

/-- Short polar windows are unchanged when viewed in the original physical chain. -/
theorem interior_polarVariation_interval (first length : ℕ) (fits : first + length ≤ N)
    (a b : Fin length) :
    interiorVariation ((P.interval first length fits).polarVariation source) a b =
      interiorVariation (P.polarVariation source)
        ⟨first + a.val, by omega⟩ ⟨first + b.val, by omega⟩ := by
  have same : (P.interval first length fits).polarVariation source =
      fun i : Fin length => P.polarVariation source ⟨first + i.val, by omega⟩ :=
    funext (P.polarVariation_interval source first length fits)
  rw [same]
  exact interiorVariation_interval (P.polarVariation source) first length fits a b

end PolygonalChain
end Unfoldings
