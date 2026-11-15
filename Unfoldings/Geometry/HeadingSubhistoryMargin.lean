module

public import Unfoldings.Geometry.ChainInterval
public import Unfoldings.Geometry.HeadingPerturbation
public import Unfoldings.Geometry.RadialChainPoints

/-! Quantitative radial margins of actual perturbed subhistories, before discarding strictness. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error : Fin n → ℝ)
  (rotated : ∀ i, Q.edge i = polarRay (error i) * P.edge i)

include rotated in
/-- Every earlier anchor is controlled by the same constants, independently of mesh size. -/
theorem radial_margin_of_heading_oscillation {ε D d : ℝ} (epsilon : 0 ≤ ε) (constant : 0 ≤ D)
    (small : D * ε < d) (oscillation : ∀ i j, |error i - error j| ≤ ε)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (P.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖P.vertex i.castSucc - P.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    ((d - D * ε) / (1 + D * ε)) *
      (‖Q.vertex i.castSucc - Q.vertex j‖ * ‖Q.edge i‖) ≤
        inner ℝ (Q.vertex i.castSucc - Q.vertex j) (Q.edge i) := by
  let fits : j.val + (i.val - j.val) ≤ n := by omega
  let A := P.interval j.val (i.val - j.val) fits
  let B := Q.interval j.val (i.val - j.val) fits
  let correction (k : Fin (i.val - j.val)) := error ⟨j.val + k.val, by omega⟩
  have edges (k : Fin (i.val - j.val)) :
      B.edge k = polarRay (correction k) * A.edge k := rotated ⟨j.val + k.val, by omega⟩
  have first : (⟨j.val, by omega⟩ : Fin (n + 1)) = j := Fin.ext rfl
  have last : (⟨j.val + (i.val - j.val), by omega⟩ : Fin (n + 1)) = i.castSucc :=
    Fin.ext (by simp only [Fin.val_castSucc]; omega)
  have endpointP : A.vertex (Fin.last (i.val - j.val)) - A.vertex 0 =
      P.vertex i.castSucc - P.vertex j := by
    change P.vertex ⟨j.val + (i.val - j.val), by omega⟩ - P.vertex ⟨j.val, by omega⟩ = _
    rw [first, last]
  have endpointQ : B.vertex (Fin.last (i.val - j.val)) - B.vertex 0 =
      Q.vertex i.castSucc - Q.vertex j := by
    change Q.vertex ⟨j.val + (i.val - j.val), by omega⟩ - Q.vertex ⟨j.val, by omega⟩ = _
    rw [first, last]
  have lengthA : A.projectedLength ≤ D * ‖A.vertex (Fin.last _) - A.vertex 0‖ := by
    rw [endpointP]
    exact length_bound j i earlier
  have marginA : d * (‖A.vertex (Fin.last _) - A.vertex 0‖ * ‖P.edge i‖) ≤
      inner ℝ (A.vertex (Fin.last _) - A.vertex 0) (P.edge i) := by
    rw [endpointP]
    exact margin j i earlier
  have estimate := A.heading_radial_margin B correction edges epsilon constant
    (fun k => oscillation ⟨j.val + k.val, by omega⟩ i) small lengthA (P.edge i) marginA
  rw [endpointQ, ← rotated i] at estimate
  exact estimate

end Unfoldings.PolygonalChain
