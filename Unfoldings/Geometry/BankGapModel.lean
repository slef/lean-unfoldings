module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Metric.PolygonalCoverGluing

/-! Complete two-bank gap pieces retain concrete convex cells and actual boundary marks. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {n : ℕ}

/-- Geometric and intrinsic data already proved for a constructed complete Jordan gap. -/
structure BankGapModel (first second : PolygonalRay ℂ n) where
  region : Set ℂ
  closed : IsClosed region
  frontier_eq : frontier region = first.carrier ∪ second.carrier
  banks_meet : first.carrier ∩ second.carrier = {first.start}
  interior_nonempty : (interior region).Nonempty
  regular_closed : closure (interior region) = region
  complete : CompleteSpace (PolygonalPoint region)
  contractible : ContractibleSpace (PolygonalPoint region)
  Cell : Type
  finite : Fintype Cell
  cells : Cell → Set ℂ
  cell_closed : ∀ i, IsClosed (cells i)
  cell_convex : ∀ i, Convex ℝ (cells i)
  cell_interior : ∀ i, (interior (cells i)).Nonempty
  cell_disjoint : ∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))
  cover : region = ⋃ i, cells i

namespace BankGapModel

variable {first second : PolygonalRay ℂ n} (M : BankGapModel first second)

instance cellFintype : Fintype M.Cell := M.finite

/-- The complete intrinsic gap is exactly its original finite convex-cell gluing. -/
def cellIsometry :
    MetricGluing.Realization (fun i => M.cells i) (MetricGluing.coincident M.cells) ≃ᵢ
      PolygonalPoint M.region :=
  MetricGluing.closedCoverIsometryEquiv M.cells M.cell_closed M.cell_convex M.cover

/-- Keep the two original banks as distinct named coordinate maps. -/
def bank (_model : BankGapModel first second) (side : Bool) : PolygonalRay ℂ n :=
  if side then second else first

/-- Every actual marked bank point lies on the original geometric gap frontier. -/
theorem bank_mem_frontier (side : Bool) (x : {z // z ∈ (M.bank side).carrier}) :
    x.val ∈ frontier M.region := by
  rw [M.frontier_eq]
  cases side
  · exact Or.inl x.property
  · exact Or.inr x.property

/-- The named bank point is its actual intrinsic point in the complete gap. -/
def bankPoint (side : Bool) (x : {z // z ∈ (M.bank side).carrier}) : PolygonalPoint M.region :=
  ⟨x.val, M.closed.frontier_subset (M.bank_mem_frontier side x)⟩

/-- The same marked point in the single finite-cell metric model. -/
def bankCellPoint (side : Bool) (x : {z // z ∈ (M.bank side).carrier}) :
    MetricGluing.Realization (fun i => M.cells i) (MetricGluing.coincident M.cells) :=
  M.cellIsometry.symm (M.bankPoint side x)

/-- Every cell representative of an actual marked bank point is a boundary point of that cell.
This derives the gap-side boundary-only attachment condition from the constructed frontier. -/
theorem bankCellPoint_boundary (side : Bool) (x : {z // z ∈ (M.bank side).carrier})
    (i : M.Cell) (p : M.cells i)
    (named : MetricGluing.of (fun i => M.cells i) (MetricGluing.coincident M.cells) i p =
      M.bankCellPoint side x) : p.val ∉ interior (M.cells i) := by
  have restored := congrArg M.cellIsometry named
  rw [bankCellPoint, M.cellIsometry.apply_symm_apply] at restored
  have position : p.val = x.val := congrArg PolygonalPoint.val restored
  intro inside
  have in_gap := (interior_mono (MetricGluing.cell_subset_of_cover M.cells M.cover i)) inside
  rw [position] at in_gap
  exact (M.bank_mem_frontier side x).2 in_gap

end BankGapModel
end Unfoldings
