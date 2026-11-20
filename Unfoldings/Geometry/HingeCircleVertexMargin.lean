module

public import Unfoldings.Geometry.HingeCircleLiftBound
public import Unfoldings.Geometry.RadialMarginSegment

/-! Link-start margins imply sharp circle-speed bounds throughout an actual hinge sweep. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (positive : 0 < angle) (outward : (R.suffix hinge).Outward) (small : angle < Real.pi)

include outward small in
/-- It suffices to test the radial margin at the first vertex of each moved link,
and at the start of the moved infinite tail. -/
theorem hingeCircleLift_last_le_of_vertex_margin
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) {m : ℝ}
    (m_pos : 0 < m) (m_le_one : m ≤ 1)
    (edges_ne : ∀ i, R.chain.edge i ≠ 0)
    (edge_margin : ∀ θ ∈ Set.Icc 0 angle, ∀ i : Fin n, hinge ≤ i.castSucc →
      let Q := R.rotateSuffix hinge θ
      let p := Q.chain.vertex i.castSucc - Q.start
      let d := Q.chain.edge i
      m * (‖p‖ * ‖d‖) ≤ inner ℝ p d)
    (tail_margin : ∀ θ ∈ Set.Icc 0 angle,
      let Q := R.rotateSuffix hinge θ
      let p := Q.chain.vertex (Fin.last n) - Q.start
      m * (‖p‖ * ‖Q.direction‖) ≤ inner ℝ p Q.direction) :
    R.hingeCircleLift hinge nonzero angle radial positive r ⟨angle, positive.le, le_rfl⟩ ≤
      (2 / m) * angle := by
  let index (i : Fin (n - hinge.val)) : Fin n := ⟨hinge.val + i.val, by omega⟩
  have edge_index (i : Fin (n - hinge.val)) :
      (R.suffix hinge).chain.edge i = R.chain.edge (index i) := rfl
  refine R.hingeCircleLift_last_le_of_margin hinge nonzero angle radial positive outward small r
    m_pos (fun i => edge_index i ▸ edges_ne (index i)) ?_ ?_
  · intro θ hθ i t
    let Q := R.rotateSuffix hinge θ
    let j := index i
    have after : hinge ≤ j.castSucc := by
      change hinge.val ≤ hinge.val + i.val
      omega
    have direction : Q.chain.edge j = polarRay θ * (R.suffix hinge).chain.edge i := by
      rw [edge_index]
      change (R.chain.rotateSuffix hinge θ).edge j = _
      rw [R.chain.rotateSuffix_edge, ite_eq_left after]
    have vertex : Q.chain.vertex j.castSucc - Q.start =
        R.chain.vertex hinge - R.start +
          polarRay θ * ((R.suffix hinge).chain.vertex i.castSucc - (R.suffix hinge).start) := by
      rw [R.rotateSuffix_start]
      change (R.chain.rotateSuffix hinge θ).vertex j.castSucc - R.start = _
      rw [R.chain.rotateSuffix_vertex_ge hinge θ _ after, complexRotation_apply, R.suffix_start]
      change R.chain.vertex hinge + polarRay θ * (R.chain.vertex j.castSucc -
        R.chain.vertex hinge) - R.start = R.chain.vertex hinge - R.start +
          polarRay θ * (R.chain.vertex j.castSucc - R.chain.vertex hinge)
      abel
    have extended := radial_margin_along_ray_of_inner m_pos.le m_le_one t.property.1
      (edge_margin θ hθ j after)
    rw [vertex, direction] at extended
    have point : (R.suffix hinge).chain.point i t =
        (R.suffix hinge).chain.vertex i.castSucc + (t : ℝ) • (R.suffix hinge).chain.edge i := by
      rw [PolygonalChain.point, AffineMap.lineMap_apply_module', add_comm, PolygonalChain.edge]
    dsimp only
    rw [point]
    have position :
        R.chain.vertex hinge - R.start +
          polarRay θ * ((R.suffix hinge).chain.vertex i.castSucc +
            (t : ℝ) • (R.suffix hinge).chain.edge i - (R.suffix hinge).start) =
        R.chain.vertex hinge - R.start +
          polarRay θ * ((R.suffix hinge).chain.vertex i.castSucc - (R.suffix hinge).start) +
          (t : ℝ) • (polarRay θ * (R.suffix hinge).chain.edge i) := by
      simp only [Complex.real_smul]
      ring
    rw [position]
    exact extended
  · intro θ hθ t
    let Q := R.rotateSuffix hinge θ
    have direction : Q.direction = polarRay θ * (R.suffix hinge).direction := rfl
    have extended := radial_margin_along_ray_of_inner m_pos.le m_le_one t.coe_nonneg
      (tail_margin θ hθ)
    have tail_eq : Q.chain.vertex (Fin.last n) - Q.start + (t : ℝ) • Q.direction =
        Q.tail t - Q.start := by
      rw [PolygonalRay.tail]
      abel
    change m * (‖Q.chain.vertex (Fin.last n) - Q.start + (t : ℝ) • Q.direction‖ * ‖Q.direction‖) ≤
      inner ℝ (Q.chain.vertex (Fin.last n) - Q.start + (t : ℝ) • Q.direction)
        Q.direction at extended
    rw [tail_eq, show Q.tail t = (R.rotateSuffix hinge θ).tail t from rfl,
      R.rotateSuffix_tail, show Q.start = R.start from R.rotateSuffix_start hinge θ,
      direction, ← congrFun (R.suffix_tail hinge) t, ← R.suffix_start hinge,
      complexRotation_apply] at extended
    have position : (R.suffix hinge).start +
        polarRay θ * ((R.suffix hinge).tail t - (R.suffix hinge).start) - R.start =
        (R.suffix hinge).start - R.start +
          polarRay θ * ((R.suffix hinge).tail t - (R.suffix hinge).start) := by abel
    rw [position] at extended
    exact extended

end Unfoldings.PolygonalRay
