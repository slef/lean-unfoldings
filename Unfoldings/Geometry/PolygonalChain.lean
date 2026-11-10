module

public import Unfoldings.Geometry.RadialSegment
public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.UnitInterval

/-! Finite polygonal chains, with radial monotonicity tested on every point of every edge. -/

@[expose] public section

namespace Unfoldings

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ)

structure PolygonalChain where
  vertex : Fin (n + 1) → E

namespace PolygonalChain

variable {E n} (P : PolygonalChain E n)

def edge (i : Fin n) : E := P.vertex i.succ - P.vertex i.castSucc

def point (i : Fin n) (t : unitInterval) : E :=
  AffineMap.lineMap (P.vertex i.castSucc) (P.vertex i.succ) (t : ℝ)

@[simp] theorem point_zero (i : Fin n) : P.point i 0 = P.vertex i.castSucc :=
  AffineMap.lineMap_apply_zero _ _

@[simp] theorem point_one (i : Fin n) : P.point i 1 = P.vertex i.succ :=
  AffineMap.lineMap_apply_one _ _

/-- Every later edge points away from every earlier vertex. This is a test, not the definition. -/
def Outward : Prop :=
  ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
    0 ≤ inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i)

/-- Distance from each earlier vertex increases throughout each later closed edge. -/
def RadiallyMonotone : Prop :=
  ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
    Monotone (fun t : unitInterval => dist (P.vertex j) (P.point i t))

/-- A coordinate-free sufficient condition for a common direction wedge of width at most pi/2. -/
def PairwiseNonnegativeEdges : Prop := ∀ i j, 0 ≤ inner ℝ (P.edge i) (P.edge j)

theorem radiallyMonotone_iff_outward : P.RadiallyMonotone ↔ P.Outward := by
  constructor
  · intro monotone j i earlier
    exact (monotone_dist_lineMap_iff _ _ _).mp (monotone j i earlier)
  · intro outward j i earlier
    exact (monotone_dist_lineMap_iff _ _ _).mpr (outward j i earlier)

/-- Pairwise nonnegative edge scalar products control every earlier vertex, without angle sums. -/
theorem PairwiseNonnegativeEdges.outward (nonnegative : P.PairwiseNonnegativeEdges) :
    P.Outward := by
  intro j i earlier
  have monotone : Monotone (fun k : Fin (n + 1) => inner ℝ (P.vertex k) (P.edge i)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have bound := nonnegative k i
    change 0 ≤ inner ℝ (P.vertex k.succ - P.vertex k.castSucc) (P.edge i) at bound
    rwa [inner_sub_left, sub_nonneg] at bound
  rw [inner_sub_left]
  exact sub_nonneg.mpr (monotone earlier)

theorem PairwiseNonnegativeEdges.radiallyMonotone (nonnegative : P.PairwiseNonnegativeEdges) :
    P.RadiallyMonotone :=
  P.radiallyMonotone_iff_outward.mpr (PairwiseNonnegativeEdges.outward P nonnegative)

/-- A genuine outward edge has a unique point at each radial distance from any earlier vertex. -/
theorem Outward.dist_point_strictMono (outward : P.Outward)
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val)
    (different : P.vertex i.castSucc ≠ P.vertex i.succ) :
    StrictMono (fun t : unitInterval => dist (P.vertex j) (P.point i t)) := by
  intro t s ordered
  exact dist_lineMap_lt_of_inner_nonneg _ _ _ (outward j i earlier) different t.property.1 ordered

end PolygonalChain
end Unfoldings
