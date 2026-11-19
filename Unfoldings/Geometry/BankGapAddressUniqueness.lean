module

public import Unfoldings.Geometry.BankGapBoundaryMap
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.PolygonalRayAddressUniqueness

/-! Nonvertex bank marks retain their original side, edge, and parameter. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ n} (M : BankGapModel first second)
  (G : OrientedBankGap first second)

include G

/-- Either named gap bank has the original outward geometry. -/
theorem bank_outward (side : Bool) : (M.bank side).Outward := by
  cases side
  · exact G.first_outward
  · exact G.second_outward

/-- The true infinite tail of either gap bank is nondegenerate. -/
theorem bank_direction_ne_zero (side : Bool) : (M.bank side).direction ≠ 0 := by
  cases side
  · exact G.first_nonzero
  · exact G.second_nonzero

/-- Away from the common source, the two literal gap banks remain distinct. -/
theorem side_eq_of_address_eq (side other : Bool) (a b : PolygonalRay.Address n)
    (away : (M.bank side).addressPoint a ≠ (M.bank side).start)
    (equal : M.addressFrontier side a = M.addressFrontier other b) : other = side := by
  have position := congrArg Subtype.val equal
  cases side <;> cases other
  · rfl
  · exfalso
    apply away
    change first.addressPoint a = second.addressPoint b at position
    have member : first.addressPoint a ∈ first.carrier ∩ second.carrier :=
      ⟨first.addressPoint_mem a, position.symm ▸ second.addressPoint_mem b⟩
    exact Set.mem_singleton_iff.mp (M.banks_meet ▸ member)
  · exfalso
    apply away
    change second.addressPoint a = first.addressPoint b at position
    have member : second.addressPoint a ∈ first.carrier ∩ second.carrier :=
      ⟨position.symm ▸ first.addressPoint_mem b, second.addressPoint_mem a⟩
    exact (Set.mem_singleton_iff.mp (M.banks_meet ▸ member)).trans G.common.symm
  · rfl

variable (genuine : ∀ side i, (M.bank side).chain.edge i ≠ 0)

include genuine

/-- A strict finite-edge mark identifies exactly its original side and address. -/
theorem addressFrontier_eq_edge_interior (side : Bool) (i : Fin n) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) (other : Bool) (a : PolygonalRay.Address n)
    (equal : M.addressFrontier other a = M.addressFrontier side (.inl (i, t))) :
    other = side ∧ a = .inl (i, t) := by
  have vertices : ∀ j : Fin n,
      (M.bank side).chain.vertex j.castSucc ≠ (M.bank side).chain.vertex j.succ :=
    fun j => Ne.symm (sub_ne_zero.mp (genuine side j))
  have same := M.side_eq_of_address_eq G side other (.inl (i, t)) a
    ((M.bank side).point_ne_start (M.bank_outward G side) vertices i t bounds.1) equal.symm
  subst other
  exact ⟨rfl, (M.bank side).address_eq_of_edge_interior (M.bank_outward G side)
    (genuine side) (M.bank_direction_ne_zero G side) i t bounds a
      (congrArg Subtype.val equal)⟩

omit genuine in
/-- A strict positive tail mark identifies exactly its original side and parameter. -/
theorem addressFrontier_eq_tail_positive (side : Bool) (t : ℝ≥0) (positive : 0 < t)
    (other : Bool) (a : PolygonalRay.Address n)
    (equal : M.addressFrontier other a = M.addressFrontier side (.inr t)) :
    other = side ∧ a = .inr t := by
  have same := M.side_eq_of_address_eq G side other (.inr t) a
    ((M.bank side).tail_ne_start (M.bank_outward G side)
      (M.bank_direction_ne_zero G side) t positive) equal.symm
  subst other
  exact ⟨rfl, (M.bank side).address_eq_of_tail_positive (M.bank_outward G side)
    (M.bank_direction_ne_zero G side) t positive a (congrArg Subtype.val equal)⟩

/-- Intrinsic strict edge marks retain their side, original edge, and original parameter. -/
theorem edgePoint_eq_edgePoint_interior (side : Bool) (i : Fin n) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) (other : Bool) (j : Fin n) (s : unitInterval)
    (equal : M.edgePoint other j s = M.edgePoint side i t) :
    other = side ∧ j = i ∧ s = t := by
  have named := M.addressFrontier_eq_edge_interior G genuine side i t bounds other
    (.inl (j, s)) (Subtype.ext (congrArg PolygonalPoint.val equal))
  exact ⟨named.1, (Prod.mk.inj (Sum.inl.inj named.2)).1,
    (Prod.mk.inj (Sum.inl.inj named.2)).2⟩

/-- A strict edge mark cannot coincide with any point of either infinite bank tail. -/
theorem tailPoint_ne_edgePoint_interior (side : Bool) (i : Fin n) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) (other : Bool) (s : ℝ≥0) :
    M.tailPoint other s ≠ M.edgePoint side i t := by
  intro equal
  have named := M.addressFrontier_eq_edge_interior G genuine side i t bounds other
    (.inr s) (Subtype.ext (congrArg PolygonalPoint.val equal))
  cases named.2

omit genuine in
/-- Positive tail marks retain their side and original unbounded parameter. -/
theorem tailPoint_eq_tailPoint_positive (side : Bool) (t : ℝ≥0) (positive : 0 < t)
    (other : Bool) (s : ℝ≥0)
    (equal : M.tailPoint other s = M.tailPoint side t) : other = side ∧ s = t := by
  have named := M.addressFrontier_eq_tail_positive G side t positive other (.inr s)
    (Subtype.ext (congrArg PolygonalPoint.val equal))
  exact ⟨named.1, Sum.inr.inj named.2⟩

omit genuine in
/-- A positive tail point cannot coincide with any finite edge on either gap bank. -/
theorem edgePoint_ne_tailPoint_positive (side : Bool) (t : ℝ≥0) (positive : 0 < t)
    (other : Bool) (i : Fin n) (s : unitInterval) :
    M.edgePoint other i s ≠ M.tailPoint side t := by
  intro equal
  have named := M.addressFrontier_eq_tail_positive G side t positive other (.inl (i, s))
    (Subtype.ext (congrArg PolygonalPoint.val equal))
  cases named.2

end Unfoldings.BankGapModel
