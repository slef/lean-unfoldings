module

public import Unfoldings.Geometry.NextEdgeRadialBlocks
public import Unfoldings.Geometry.HeadingBudgetInterval
public import Unfoldings.Geometry.RadialChainLength
public import Unfoldings.Geometry.RadialChainPoints

/-! Weighted local comparisons preserve quantitative radial order on every actual subhistory. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {N : ℕ} (P Q : PolygonalChain ℂ N) (source : ℂ)
  (error stretch : Fin N → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)
  {S B δ γ d : ℝ} (speed : 1 ≤ S) (budget : 0 ≤ B) (width : 0 < δ)
  (lower : ∀ i, 1 ≤ stretch i) (upper : ∀ i, stretch i ≤ S)
  (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1)
  (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
    inner ℝ (P.vertex i.castSucc - source) (P.edge i))
  (window : ∀ i j, i ≤ j → interiorVariation (P.polarVariation source) i j < δ →
    |error i - error j| ≤ B)
  (all_anchors : ∀ (j : Fin (N + 1)) (i : Fin N), j.val ≤ i.val →
    d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))
  (small : radialBlockError S B γ⁻¹ (Real.sqrt (1 - γ ^ 2)) δ < d)

include changed speed budget width lower upper gamma_positive gamma_small margin window
  all_anchors small

/-- Every earlier original anchor retains an explicit margin against each later lifted edge. -/
theorem radialBlock_subhistory_margin (j : Fin (N + 1)) (i : Fin N)
    (earlier : j.val ≤ i.val) :
    ((d - radialBlockError S B γ⁻¹ (Real.sqrt (1 - γ ^ 2)) δ) /
      (1 + radialBlockError S B γ⁻¹ (Real.sqrt (1 - γ ^ 2)) δ)) *
      (‖Q.vertex i.castSucc - Q.vertex j‖ * ‖Q.edge i‖) ≤
        inner ℝ (Q.vertex i.castSucc - Q.vertex j) (Q.edge i) := by
  let m := i.val - j.val
  have fits : j.val + (m + 1) ≤ N := by dsimp only [m]; omega
  let A := P.interval j.val (m + 1) fits
  let D := Q.interval j.val (m + 1) fits
  let index (k : Fin (m + 1)) : Fin N := ⟨j.val + k.val, by omega⟩
  have local_margin := P.interval_radial_margin source j.val (m + 1) fits margin
  have local_changed (k : Fin (m + 1)) :
      D.edge k = (stretch (index k) : ℂ) * polarRay (error (index k)) * A.edge k := by
    simpa only [A, D, interval_edge, index] using changed (index k)
  have local_window (a b : Fin (m + 1)) (ordered : a ≤ b)
      (short : interiorVariation (A.polarVariation source) a b < δ) :
      |error (index a) - error (index b)| ≤ B := by
    apply window (index a) (index b) (by change j.val + a.val ≤ j.val + b.val; omega)
    rwa [P.interior_polarVariation_interval source] at short
  have prefix_bound (k : Fin (m + 1)) : (A.interval 0 k.val (by omega)).projectedLength ≤
      γ⁻¹ * ‖A.vertex k.castSucc - source‖ :=
    A.radial_prefix_projectedLength source gamma_positive gamma_small local_margin k.castSucc
  have length_bound : (A.interval 0 m (by omega)).projectedLength ≤
      γ⁻¹ * ‖A.vertex (Fin.last m).castSucc - A.vertex 0‖ := by
    have bound := (A.interval 0 m (by omega)).radial_projectedLength_le_chord source
      gamma_positive gamma_small (A.interval_radial_margin source 0 m (by omega) local_margin)
    simpa only [interval, Nat.zero_add, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Fin.val_zero, Fin.mk_zero] using bound
  have start (X : PolygonalChain ℂ N) :
      (X.interval j.val (m + 1) fits).vertex 0 = X.vertex j := by
    apply congrArg X.vertex
    apply Fin.ext
    simp only [Fin.val_zero, Nat.add_zero]
  have finish (X : PolygonalChain ℂ N) :
      (X.interval j.val (m + 1) fits).vertex (Fin.last m).castSucc = X.vertex i.castSucc := by
    apply congrArg X.vertex
    apply Fin.ext
    change j.val + m = i.val
    dsimp only [m]
    omega
  have next (X : PolygonalChain ℂ N) :
      (X.interval j.val (m + 1) fits).edge (Fin.last m) = X.edge i := by
    rw [interval_edge]
    apply congrArg X.edge
    apply Fin.ext
    change j.val + m = i.val
    dsimp only [m]
    omega
  have endpoint_margin : d * (‖A.vertex (Fin.last m).castSucc - A.vertex 0‖ *
      ‖A.edge (Fin.last m)‖) ≤
      inner ℝ (A.vertex (Fin.last m).castSucc - A.vertex 0) (A.edge (Fin.last m)) := by
    simpa only [A, start, finish, next] using all_anchors j i earlier
  have estimate := A.next_edge_radial_margin D source
    (fun k => error (index k)) (fun k => stretch (index k)) local_changed speed budget
    (inv_nonneg.mpr gamma_positive.le) width (fun k => lower (index k))
    (fun k => upper (index k)) gamma_positive.le gamma_small local_margin prefix_bound
    local_window length_bound small endpoint_margin
  simpa only [D, start, finish, next] using estimate

/-- A positive remaining radial margin makes the complete lifted chain outward. -/
theorem radialBlock_outward : Q.Outward := by
  have nonnegative := radialBlockError_nonneg speed budget (inv_nonneg.mpr gamma_positive.le)
    (Real.sqrt_nonneg (1 - γ ^ 2)) width
  have loss_nonnegative : 0 ≤
      (d - radialBlockError S B γ⁻¹ (Real.sqrt (1 - γ ^ 2)) δ) /
      (1 + radialBlockError S B γ⁻¹ (Real.sqrt (1 - γ ^ 2)) δ) :=
    div_nonneg (sub_nonneg.mpr small.le) (by positivity)
  intro j i earlier
  have estimate := P.radialBlock_subhistory_margin Q source error stretch changed speed budget
    width lower upper gamma_positive gamma_small margin window all_anchors small j i earlier
  exact (mul_nonneg loss_nonnegative
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate

/-- Radial order includes all earlier points inside edges and every later pair of points. -/
theorem radialBlock_globallyRadiallyMonotone : Q.GloballyRadiallyMonotone :=
  Outward.globallyRadiallyMonotone Q (P.radialBlock_outward Q source error stretch changed speed
    budget width lower upper gamma_positive gamma_small margin window all_anchors small)

end Unfoldings.PolygonalChain
