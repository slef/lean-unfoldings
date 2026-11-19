module

public import Unfoldings.Geometry.PolygonalRayTransfer
public import Unfoldings.Geometry.RadialRayEdgePoints

/-! Original bank addresses are unique away from vertices and the tail join. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n) (outward : R.Outward)
  (genuine : ∀ i : Fin n, R.chain.edge i ≠ 0) (nonzero : R.direction ≠ 0)

include outward genuine nonzero

/-- A strict finite-edge point has just its original edge and parameter as an address.
Closed endpoints deliberately retain their multiple addresses. -/
theorem address_eq_of_edge_interior (i : Fin n) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) (a : Address n)
    (equal : R.addressPoint a = R.chain.point i t) : a = .inl (i, t) := by
  have vertices : ∀ j : Fin n, R.chain.vertex j.castSucc ≠ R.chain.vertex j.succ :=
    fun j => Ne.symm (sub_ne_zero.mp (genuine j))
  cases a with
  | inl p =>
    obtain ⟨j, s⟩ := p
    have same : j = i := by
      by_contra different
      apply R.point_not_mem_other_segment outward vertices i t bounds j different
      rw [← equal]
      exact (Path.range_segment _ _).subset ⟨s, rfl⟩
    subst j
    have parameter : s = t := (R.edge_radius_strictMono outward vertices i).injective
      (congrArg (dist R.start) equal)
    subst s
    rfl
  | inr s =>
    exact (R.point_not_mem_tail outward vertices nonzero i t bounds.2 ⟨s, equal⟩).elim

omit genuine in
/-- Every strict positive point of the actual tail has a unique original address. -/
theorem address_eq_of_tail_positive (t : ℝ≥0) (positive : 0 < t) (a : Address n)
    (equal : R.addressPoint a = R.tail t) : a = .inr t := by
  cases a with
  | inl p =>
    have finite_member : R.chain.point p.1 p.2 ∈ Set.range R.chain.path := by
      rw [R.chain.path_range]
      exact Or.inr (Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩)
    have upper := R.prefix_radius_le outward finite_member
    have lower := R.tail_radius_strictMono outward nonzero positive
    dsimp only at lower
    dsimp only [addressPoint] at equal
    rw [R.tail_zero, ← equal] at lower
    exact ((not_lt_of_ge upper) lower).elim
  | inr s =>
    have same : s = t := (R.tail_radius_strictMono outward nonzero).injective
      (congrArg (dist R.start) equal)
    exact congrArg Sum.inr same

omit genuine in
/-- A positive tail parameter cannot represent the source, including a bank with no edges. -/
theorem tail_ne_start (t : ℝ≥0) (positive : 0 < t) : R.tail t ≠ R.start := by
  intro equal
  have lower := R.tail_radius_strictMono outward nonzero positive
  dsimp only at lower
  rw [equal, dist_self] at lower
  exact (not_lt_of_ge dist_nonneg) lower

end Unfoldings.PolygonalRay
