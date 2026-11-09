module

public import Unfoldings.Path.Straight
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact additive distances along every finite monotone geodesic partition. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.sum_partition_edist (geodesic : p.IsGeodesic) {n : ℕ}
    (time : Fin (n + 1) → unitInterval) (ordered : Monotone time) :
    ∑ i : Fin n, edist (p (time i.castSucc)) (p (time i.succ)) =
      edist (p (time 0)) (p (time (Fin.last n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have first := ih (fun i => time i.castSucc)
      (fun i j h => ordered (by exact h))
    change (∑ i : Fin n, edist (p (time i.castSucc.castSucc)) (p (time i.succ.castSucc))) +
      edist (p (time (Fin.last n).castSucc)) (p (time (Fin.last (n + 1)))) = _
    rw [first]
    exact geodesic.edist_add_edist_eq
      (ordered (Fin.zero_le _)) (ordered (Fin.le_last _))

end Path
