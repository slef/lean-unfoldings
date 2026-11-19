module

public import Unfoldings.Geometry.RadialChain

/-! Radial chains with genuine edges retain only the usual shared-endpoint identifications. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  (P : PolygonalChain E n) {origin : E}
  (radial : P.RadialFrom origin 0) (genuine : ∀ i, P.edge i ≠ 0)

include radial genuine

/-- Source distance strictly increases on each genuine radial edge. -/
theorem RadialFrom.point_radius_strictMono (i : Fin n) :
    StrictMono (fun t : unitInterval => dist origin (P.point i t)) := by
  intro s t ordered
  apply dist_lineMap_lt_of_inner_nonneg
  · exact (monotone_dist_lineMap_iff _ _ _).mp (radial i (Nat.zero_le _))
  · exact Ne.symm (sub_ne_zero.mp (genuine i))
  · exact s.property.1
  · exact ordered

/-- Genuine radial edges give a strictly ordered list of vertex radii. -/
theorem RadialFrom.vertex_radius_strictMono :
    StrictMono (fun i => dist origin (P.vertex i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  simpa only [point_zero, point_one] using
    RadialFrom.point_radius_strictMono P radial genuine i (show (0 : unitInterval) < 1 from
      zero_lt_one)

/-- Equality of points on an embedded radial chain transfers to any chain with the same
edge indices. Adjacent closed edges can meet at their shared endpoint. -/
theorem RadialFrom.transfer_point_eq (Q : PolygonalChain F n)
    (i j : Fin n) (t s : unitInterval) (equal : P.point i t = P.point j s) :
    Q.point i t = Q.point j s := by
  have forward (i j : Fin n) (t s : unitInterval) (before : i < j)
      (equal : P.point i t = P.point j s) : Q.point i t = Q.point j s := by
    have first := (RadialFrom.point_radius_strictMono P radial genuine i).monotone
      (show t ≤ (1 : unitInterval) from t.property.2)
    have last := (RadialFrom.point_radius_strictMono P radial genuine j).monotone
      (show (0 : unitInterval) ≤ s from s.property.1)
    have vertices := RadialFrom.vertex_radius_strictMono P radial genuine
    have index_order : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    have middle := vertices.monotone index_order
    rw [point_one] at first
    rw [point_zero] at last
    have radius : dist origin (P.point i t) = dist origin (P.point j s) := congrArg _ equal
    have at_one : t = 1 := (RadialFrom.point_radius_strictMono P radial genuine i).injective (by
      rw [point_one]
      linarith)
    have at_zero : s = 0 := (RadialFrom.point_radius_strictMono P radial genuine j).injective (by
      rw [point_zero]
      linarith)
    have adjacent : i.succ = j.castSucc := vertices.injective (by linarith)
    rw [at_one, at_zero, Q.point_one, Q.point_zero, adjacent]
  rcases lt_trichotomy i j with before | same | after
  · exact forward i j t s before equal
  · subst j
    have parameter : t = s := (RadialFrom.point_radius_strictMono P radial genuine i).injective
      (congrArg _ equal)
    exact congrArg (Q.point i) parameter
  · exact (forward j i s t after equal.symm).symm

/-- A point equal to the final vertex has the final edge's endpoint parameter. -/
theorem RadialFrom.point_eq_last (i : Fin n) (t : unitInterval)
    (equal : P.point i t = P.vertex (Fin.last n)) :
    i.succ = Fin.last n ∧ t = 1 := by
  have edge_radius := (RadialFrom.point_radius_strictMono P radial genuine i).monotone
      (show t ≤ (1 : unitInterval) from t.property.2)
  rw [point_one] at edge_radius
  have vertices := RadialFrom.vertex_radius_strictMono P radial genuine
  have final_radius := vertices.monotone (Fin.le_last i.succ)
  have radius := congrArg (dist origin) equal
  have index : i.succ = Fin.last n := vertices.injective (by linarith)
  refine ⟨index, (RadialFrom.point_radius_strictMono P radial genuine i).injective ?_⟩
  rw [point_one, index, equal]

/-- A point equal to the initial vertex has the first edge's initial parameter. -/
theorem RadialFrom.point_eq_first (i : Fin n) (t : unitInterval)
    (equal : P.point i t = P.vertex 0) :
    i.castSucc = 0 ∧ t = 0 := by
  have edge_radius := (RadialFrom.point_radius_strictMono P radial genuine i).monotone
      (show (0 : unitInterval) ≤ t from t.property.1)
  rw [point_zero] at edge_radius
  have vertices := RadialFrom.vertex_radius_strictMono P radial genuine
  have first_radius := vertices.monotone (Fin.zero_le i.castSucc)
  have radius := congrArg (dist origin) equal
  have index : i.castSucc = 0 := vertices.injective (by linarith)
  refine ⟨index, (RadialFrom.point_radius_strictMono P radial genuine i).injective ?_⟩
  rw [point_zero, index, equal]

end Unfoldings.PolygonalChain
