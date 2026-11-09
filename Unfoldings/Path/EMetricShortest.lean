module

public import Unfoldings.Path.Shortest
public import Unfoldings.Path.FiniteComponent

/-! Shortest-path existence for compact extended metric spaces, including disconnected ones. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [EMetricSpace X] [CompactSpace X] {a b : X}

/-- A rectifiable path in a compact extended metric space admits a shortest replacement. -/
theorem exists_lengthMinimizing_emetric (p : Path a b) (finite : p.eLength ≠ ⊤) :
    ∃ q : Path a b, q.IsLengthMinimizing ∧ q.eLength ≠ ⊤ ∧ LipschitzWith q.eLength.toNNReal q := by
  have start : edist a a ≠ ⊤ := by simp
  let lifted := p.toFiniteComponent start finite
  have lifted_finite : lifted.eLength ≠ ⊤ := by
    simpa only [lifted, eLength_toFiniteComponent] using finite
  obtain ⟨q, minimal, qfinite, speed⟩ := lifted.exists_lengthMinimizing_lipschitz lifted_finite
  let result : Path a b := q.map continuous_subtype_val
  have length : result.eLength = q.eLength :=
    q.eLength_map_isometry (Unfoldings.FiniteComponent.val_isometry a)
  have minimal' : result.IsLengthMinimizing := by
    intro other
    by_cases infinite : other.eLength = ⊤
    · rw [infinite]
      exact le_top
    · have bound := minimal (other.toFiniteComponent start infinite)
      rw [eLength_toFiniteComponent] at bound
      exact length.le.trans bound
  have speed' : LipschitzWith q.eLength.toNNReal result := by
    change LipschitzWith q.eLength.toNNReal (Subtype.val ∘ q)
    simpa only [one_mul] using (Unfoldings.FiniteComponent.val_isometry a).lipschitzWith.comp speed
  refine ⟨result, minimal', ?_, ?_⟩
  · rwa [length]
  · rwa [length]

end Path
