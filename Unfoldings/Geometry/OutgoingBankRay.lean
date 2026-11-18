module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.RadialSubhistoryLength

/-! Continue a finite bank along its actual last outgoing edge, retaining all earlier bends. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E (n + 1))

/-- The final edge becomes a complete ray; all preceding vertices retain their literal positions. -/
def outgoingRay : PolygonalRay E n where
  chain := ⟨fun j => P.vertex j.castSucc⟩
  direction := P.edge (Fin.last n)

omit [InnerProductSpace ℝ E] in
@[simp] theorem outgoingRay_vertex (j : Fin (n + 1)) :
    P.outgoingRay.chain.vertex j = P.vertex j.castSucc := rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem outgoingRay_edge (i : Fin n) :
    P.outgoingRay.chain.edge i = P.edge i.castSucc := rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem outgoingRay_direction : P.outgoingRay.direction = P.edge (Fin.last n) := rfl

/-- Every original finite bank point remains on the continued bank. -/
theorem point_mem_outgoingRay_carrier (i : Fin (n + 1)) (t : unitInterval) :
    P.point i t ∈ P.outgoingRay.carrier := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply Or.inr
    refine ⟨⟨t.val, t.property.1⟩, ?_⟩
    change P.vertex (Fin.last n).castSucc + t.val • P.edge (Fin.last n) = _
    simp only [point, AffineMap.lineMap_apply_module', edge]
    abel
  · apply Or.inl
    rw [P.outgoingRay.chain.path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨j, t, rfl⟩)

/-- The actual outgoing extension preserves source-radial order. -/
theorem outgoingRay_outward (outward : P.Outward) : P.outgoingRay.Outward := by
  constructor
  · intro i _
    apply (monotone_dist_lineMap_iff _ _ _).mpr
    exact outward 0 i.castSucc (Nat.zero_le _)
  · exact outward 0 (Fin.last n) (Nat.zero_le _)

variable {γ : ℝ}
  (margin : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
    γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))

include margin in
/-- All finite continued-bank margins are inherited from the original actual bank. -/
theorem outgoingRay_margin (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    γ * (‖P.outgoingRay.chain.vertex i.castSucc - P.outgoingRay.chain.vertex j‖ *
      ‖P.outgoingRay.chain.edge i‖) ≤
      inner ℝ (P.outgoingRay.chain.vertex i.castSucc - P.outgoingRay.chain.vertex j)
        (P.outgoingRay.chain.edge i) := margin j.castSucc i.castSucc earlier

include margin in
/-- The true last outgoing edge has the same margin against every earlier bank vertex. -/
theorem outgoingRay_tail_margin (j : Fin (n + 1)) :
    γ * (‖P.outgoingRay.chain.vertex (Fin.last n) - P.outgoingRay.chain.vertex j‖ *
      ‖P.outgoingRay.direction‖) ≤
      inner ℝ (P.outgoingRay.chain.vertex (Fin.last n) - P.outgoingRay.chain.vertex j)
        P.outgoingRay.direction :=
  margin j.castSucc (Fin.last n) (Nat.le_of_lt_succ j.isLt)

end Unfoldings.PolygonalChain
