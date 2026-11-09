module

public import Unfoldings.Complex.SeamWord

/-! Exact propagation of rigid motions along a finite oriented seam word. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem wordPlacement_on_motions {n : ℕ} (letters : Fin n → C.Seam × Bool)
    (motions : Fin (n + 1) → (Plane ≃ᵃⁱ[ℝ] Plane))
    (joined : ∀ i, motions i.succ =
      (C.seamTransition (letters i).1 (letters i).2).trans (motions i.castSucc)) :
    motions (Fin.last n) = C.wordPlacement (List.ofFn letters) (motions 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, wordPlacement]
    have result := ih (fun i => letters i.succ) (fun i => motions i.succ) (fun i => joined i.succ)
    exact result.trans (congrArg (C.wordPlacement (List.ofFn (fun i : Fin n => letters i.succ)))
      (joined 0))

end Unfoldings.TriangleComplex
