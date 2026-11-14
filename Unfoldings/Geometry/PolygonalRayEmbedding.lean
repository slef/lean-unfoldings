module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.BankRadialOrder

/-! Source-radial tests produce genuine proper embedded polygonal rays. -/

@[expose] public section

noncomputable section

open Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n)

/-- Constant edges are harmless: equality of radii forces equality of actual points. -/
theorem prefix_eq_of_radius_eq (outward : R.Outward) {x y : E}
    (hx : x ∈ Set.range R.chain.path) (hy : y ∈ Set.range R.chain.path)
    (radius : dist R.start x = dist R.start y) : x = y := by
  have xcover := R.chain.path_range.subset hx
  have ycover := R.chain.path_range.subset hy
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at xcover ycover
  rcases xcover with origin | ⟨i, t, rfl⟩
  · have same : x = R.start := Set.mem_singleton_iff.mp origin
    rw [same, dist_self] at radius
    exact same.trans (dist_eq_zero.mp radius.symm)
  · rcases ycover with origin | ⟨j, s, rfl⟩
    · have same : y = R.start := Set.mem_singleton_iff.mp origin
      rw [same, dist_self] at radius
      exact (dist_eq_zero.mp radius).symm.trans same.symm
    · rcases PolygonalChain.before_total i j t s with ordered | ordered
      · exact PolygonalChain.RadialFrom.point_eq_of_dist_eq R.chain outward.1 i j t s
          (Nat.zero_le _) ordered radius
      · exact (PolygonalChain.RadialFrom.point_eq_of_dist_eq R.chain outward.1 j i s t
          (Nat.zero_le _) ordered radius.symm).symm

theorem prefix_radius_le (outward : R.Outward) {x : E}
    (hx : x ∈ Set.range R.chain.path) :
    dist R.start x ≤ dist R.start (R.chain.vertex (Fin.last n)) := by
  have cover := R.chain.path_range.subset hx
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
  rcases cover with origin | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp origin]
    simp only [start, dist_self]
    exact dist_nonneg
  · have first := outward.1 i (Nat.zero_le _) (show t ≤ (1 : unitInterval) from t.property.2)
    change dist R.start (R.chain.point i t) ≤ dist R.start (R.chain.point i 1) at first
    rw [R.chain.point_one] at first
    exact first.trans (PolygonalChain.RadialFrom.dist_vertices_le R.chain outward.1
      i.succ (Fin.last n)
      (Fin.zero_le _) (Fin.le_last _))

/-- The source-centered radius is injective on the entire bank, including its infinite end. -/
theorem eq_of_radius_eq (outward : R.Outward) (nonzero : R.direction ≠ 0) {x y : E}
    (hx : x ∈ R.carrier) (hy : y ∈ R.carrier)
    (radius : dist R.start x = dist R.start y) : x = y := by
  have mixed {p : E} (hp : p ∈ Set.range R.chain.path) (t : ℝ≥0)
      (same : dist R.start p = dist R.start (R.tail t)) : p = R.tail t := by
    have lower := (R.tail_radius_strictMono outward nonzero).monotone
      (show (0 : ℝ≥0) ≤ t from zero_le)
    have upper := R.prefix_radius_le outward hp
    rw [R.tail_zero] at lower
    have equality : dist R.start (R.tail t) = dist R.start (R.tail 0) := by
      rw [R.tail_zero]
      linarith
    have at_zero := (R.tail_radius_strictMono outward nonzero).injective equality
    subst t
    exact R.prefix_eq_of_radius_eq outward hp
      ⟨1, by simpa only [R.tail_zero] using R.chain.path.target⟩ same
  rcases hx with hx | ⟨t, rfl⟩ <;> rcases hy with hy | ⟨s, rfl⟩
  · exact R.prefix_eq_of_radius_eq outward hx hy radius
  · exact mixed hx s radius
  · exact (mixed hy t radius.symm).symm
  · exact congrArg R.tail ((R.tail_radius_strictMono outward nonzero).injective radius)

/-- Every nonnegative radius is attained by one actual point, not an extrapolated bank point. -/
theorem exists_radius (nonzero : R.direction ≠ 0) (r : ℝ≥0) :
    ∃ x ∈ R.carrier, dist R.start x = (r : ℝ) := by
  by_cases before : (r : ℝ) ≤ dist R.start (R.chain.vertex (Fin.last n))
  · have covered := intermediate_value_univ (0 : unitInterval) (1 : unitInterval)
      (f := fun t => dist R.start (R.chain.path t)) (by fun_prop)
    have endpoints : (r : ℝ) ∈ Set.Icc (dist R.start (R.chain.path 0))
        (dist R.start (R.chain.path 1)) := by
      simpa only [Set.mem_Icc, Path.source, Path.target, start, dist_self] using
        And.intro r.coe_nonneg before
    obtain ⟨t, ht⟩ := covered endpoints
    exact ⟨R.chain.path t, Or.inl ⟨t, rfl⟩, ht⟩
  · obtain ⟨s, hs⟩ := R.exists_tail_radius_ge nonzero r
    have covered := intermediate_value_univ (0 : ℝ≥0) s
      (f := fun t => dist R.start (R.tail t)) (continuous_const.dist R.continuous_tail)
    obtain ⟨t, ht⟩ := covered ⟨by simpa only [R.tail_zero] using (le_of_not_ge before), hs⟩
    exact ⟨R.tail t, R.tail_mem t, ht⟩

/-- Radial coordinates on the actual carrier; no parameter injectivity is assumed. -/
def radius : R.carrier → ℝ≥0 := fun x => nndist R.start x.val

theorem continuous_radius : Continuous R.radius := by
  unfold radius
  fun_prop

theorem radius_bijective (outward : R.Outward) (nonzero : R.direction ≠ 0) :
    Function.Bijective R.radius := by
  constructor
  · intro x y same
    apply Subtype.ext
    apply R.eq_of_radius_eq outward nonzero x.property y.property
    exact congrArg ((↑) : ℝ≥0 → ℝ) same
  · intro r
    obtain ⟨x, hx, same⟩ := R.exists_radius nonzero r
    exact ⟨⟨x, hx⟩, NNReal.eq same⟩

variable [ProperSpace E]

theorem isProperMap_radius (nonzero : R.direction ≠ 0) : IsProperMap R.radius :=
  (isProperMap_nndist R.start).comp
    (R.isClosed_carrier nonzero).isClosedEmbedding_subtypeVal.isProperMap

/-- A source-radially monotone polygonal ray is homeomorphic to the closed half-line. -/
def radialHomeomorph (outward : R.Outward) (nonzero : R.direction ≠ 0) :
    R.carrier ≃ₜ ℝ≥0 :=
  (Equiv.ofBijective R.radius (R.radius_bijective outward nonzero)).toHomeomorphOfContinuousClosed
    R.continuous_radius (R.isProperMap_radius nonzero).isClosedMap

@[simp] theorem radialHomeomorph_apply (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (x : R.carrier) : R.radialHomeomorph outward nonzero x = nndist R.start x.val := rfl

end Unfoldings.PolygonalRay
