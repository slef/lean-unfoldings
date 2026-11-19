module

public import Unfoldings.Geometry.BankGapModel
public import Unfoldings.Geometry.PolygonalRayFibers

/-! Map a gap's two actual boundary banks to one physical bank with finite fibers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.BankGapModel

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  {first second : PolygonalRay ℂ n} (M : BankGapModel first second)

/-- The first actual bank point as a point of the full geometric frontier. -/
def firstFrontier (x : first.carrier) : frontier M.region :=
  ⟨x.val, M.bank_mem_frontier false x⟩

/-- The second actual bank point as a point of the full geometric frontier. -/
def secondFrontier (x : second.carrier) : frontier M.region :=
  ⟨x.val, M.bank_mem_frontier true x⟩

/-- Collapse both banks to their original physical path using the original addresses.
Interior gap points are outside the domain of this boundary map. -/
def frontierMap (Q : PolygonalRay F n) (z : frontier M.region) : Q.carrier := by
  classical
  exact if member : z.val ∈ first.carrier then first.mapCarrier Q ⟨z.val, member⟩
    else second.mapCarrier Q ⟨z.val,
      ((M.frontier_eq ▸ z.property) : z.val ∈ first.carrier ∪ second.carrier).resolve_left member⟩

/-- The first bank keeps every original finite edge and infinite tail parameter. -/
theorem frontierMap_first (Q : PolygonalRay F n) (x : first.carrier) :
    M.frontierMap Q (M.firstFrontier x) = first.mapCarrier Q x := by
  unfold frontierMap
  split
  · rfl
  · rename_i absent
    exact (absent x.property).elim

/-- Every original finite or infinite bank address as a literal gap frontier point. -/
def addressFrontier (side : Bool) (a : PolygonalRay.Address n) : frontier M.region :=
  ⟨(M.bank side).addressPoint a,
    M.bank_mem_frontier side ⟨_, (M.bank side).addressPoint_mem a⟩⟩

variable (first_outward : first.Outward) (first_genuine : ∀ i, first.chain.edge i ≠ 0)
  (first_nonzero : first.direction ≠ 0) (second_outward : second.Outward)
  (second_genuine : ∀ i, second.chain.edge i ≠ 0) (second_nonzero : second.direction ≠ 0)
  (common : second.start = first.start)

include first_outward first_genuine first_nonzero second_outward second_genuine second_nonzero
  common

/-- The second bank has the same original physical parametrization. The only ambiguity
in choosing a bank is their common source, which both transports preserve. -/
theorem frontierMap_second (Q : PolygonalRay F n) (x : second.carrier) :
    M.frontierMap Q (M.secondFrontier x) = second.mapCarrier Q x := by
  unfold frontierMap
  split
  · rename_i member
    have intersection : x.val ∈ first.carrier ∩ second.carrier := ⟨member, x.property⟩
    rw [M.banks_meet] at intersection
    have source : x.val = first.start := Set.mem_singleton_iff.mp intersection
    have left : (⟨x.val, member⟩ : first.carrier) = ⟨first.start, first.start_mem⟩ :=
      Subtype.ext source
    have right : x = ⟨second.start, second.start_mem⟩ :=
      Subtype.ext (source.trans common.symm)
    change first.mapCarrier Q ⟨x.val, member⟩ = second.mapCarrier Q x
    rw [left, right]
    exact (first.mapCarrier_start first_outward first_genuine first_nonzero Q).trans
      (second.mapCarrier_start second_outward second_genuine second_nonzero Q).symm
  · rfl

/-- Both banks keep every original finite edge and whole-tail address in the same
physical target, including their common source and every shared endpoint. -/
theorem frontierMap_address (Q : PolygonalRay F n) (side : Bool)
    (a : PolygonalRay.Address n) :
    M.frontierMap Q (M.addressFrontier side a) =
      ⟨Q.addressPoint a, Q.addressPoint_mem a⟩ := by
  cases side
  · exact (M.frontierMap_first Q _).trans
      (first.mapCarrier_address first_outward first_genuine first_nonzero Q a)
  · exact (M.frontierMap_second first_outward first_genuine first_nonzero second_outward
      second_genuine second_nonzero common Q _).trans
      (second.mapCarrier_address second_outward second_genuine second_nonzero Q a)

/-- The entire gap frontier has finite fibers over a genuine physical bank. This uses
only the two-bank geometry and original parameters, with no nonoverlap assumption. -/
theorem finite_frontierMap_fiber (Q : PolygonalRay F n)
    (target_genuine : ∀ i, Q.chain.edge i ≠ 0) (target_nonzero : Q.direction ≠ 0)
    (y : Q.carrier) : {z : frontier M.region | M.frontierMap Q z = y}.Finite := by
  have left_finite := (first.finite_mapCarrier_fiber first_outward first_genuine first_nonzero
    Q target_genuine target_nonzero y).image M.firstFrontier
  have right_finite := (second.finite_mapCarrier_fiber second_outward second_genuine second_nonzero
    Q target_genuine target_nonzero y).image M.secondFrontier
  apply (left_finite.union right_finite).subset
  intro z named
  have member : z.val ∈ first.carrier ∪ second.carrier := M.frontier_eq ▸ z.property
  rcases member with member | member
  · refine Or.inl ⟨⟨z.val, member⟩, ?_, rfl⟩
    exact (M.frontierMap_first Q ⟨z.val, member⟩).symm.trans named
  · refine Or.inr ⟨⟨z.val, member⟩, ?_, rfl⟩
    exact (M.frontierMap_second first_outward first_genuine first_nonzero second_outward
      second_genuine second_nonzero common Q ⟨z.val, member⟩).symm.trans named

end Unfoldings.BankGapModel
