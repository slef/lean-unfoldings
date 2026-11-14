module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.ChainSplit

/-! Infinite suffixes retain the hinge, subsequent finite edges, and the original tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n)

def suffix (hinge : Fin (n + 1)) : PolygonalRay E (n - hinge.val) where
  chain := R.chain.interval hinge.val (n - hinge.val) (by omega)
  direction := R.direction

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem suffix_start (hinge : Fin (n + 1)) :
    (R.suffix hinge).start = R.chain.vertex hinge := rfl

@[simp] theorem suffix_tail (hinge : Fin (n + 1)) : (R.suffix hinge).tail = R.tail := by
  funext t
  unfold tail suffix
  rw [R.chain.interval_last]
  have same : (⟨hinge.val + (n - hinge.val), by omega⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  rw [same]

theorem carrier_split (hinge : Fin (n + 1)) :
    R.carrier = Set.range (R.chain.interval 0 hinge.val (by omega)).path ∪
      (R.suffix hinge).carrier := by
  unfold carrier
  rw [R.chain.path_range_split hinge, ← Set.union_assoc, R.suffix_tail]
  rfl

/-- The whole-chain outward test controls every infinite suffix from its own hinge. -/
theorem suffix_outward (hinge : Fin (n + 1)) (finite : R.chain.Outward)
    (tail_outward : 0 ≤ inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex hinge) R.direction) :
    (R.suffix hinge).Outward := by
  constructor
  · intro i _
    change Monotone (fun t : unitInterval =>
      dist (R.suffix hinge).start
        ((R.chain.interval hinge.val (n - hinge.val) (by omega)).point i t))
    simp only [suffix_start, R.chain.interval_point]
    exact (R.chain.radiallyMonotone_iff_outward.mpr finite) hinge
      ⟨hinge.val + i.val, by omega⟩ (by change hinge.val ≤ hinge.val + i.val; omega)
  · change 0 ≤ inner ℝ
      ((R.chain.interval hinge.val (n - hinge.val) (by omega)).vertex (Fin.last (n - hinge.val)) -
        (R.suffix hinge).start) R.direction
    rw [R.chain.interval_last, R.suffix_start]
    have same : (⟨hinge.val + (n - hinge.val), by omega⟩ : Fin (n + 1)) = Fin.last n :=
      Fin.ext (by simp only [Fin.val_last]; omega)
    rw [same]
    exact tail_outward

end Unfoldings.PolygonalRay
