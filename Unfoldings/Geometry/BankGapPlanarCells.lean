module

public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Metric.PolygonalBoundaryCover
public import Unfoldings.Metric.PolygonalRigid
public import Unfoldings.Geometry.ComplexArea

/-! Canonical planar coordinates retain each gap's finite cells and boundary-only seams. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ n} (M : BankGapModel first second)

/-- The same actual gap region in the common real Euclidean plane. -/
def planarRegion : Set Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph '' M.region

/-- Every gap cell retains its literal rigid real-plane coordinates. -/
def planarCells (i : M.Cell) : Set Plane :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph '' M.cells i

theorem planarCells_closed (i : M.Cell) : IsClosed (M.planarCells i) :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.isClosedMap _ (M.cell_closed i)

theorem planarCells_convex (i : M.Cell) : Convex ℝ (M.planarCells i) :=
  Convex.affine_image Complex.orthonormalBasisOneI.repr.toAffineMap (M.cell_convex i)

theorem planarCells_full (i : M.Cell) : (interior (M.planarCells i)).Nonempty := by
  rw [planarCells, ← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_interior]
  exact (M.cell_interior i).image _

theorem planarCells_disjoint (i j : M.Cell) (different : i ≠ j) :
    Disjoint (interior (M.planarCells i)) (interior (M.planarCells j)) := by
  rw [planarCells, planarCells,
    ← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_interior,
    ← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_interior]
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, first⟩ ⟨b, hb, last⟩
  have same : a = b := Complex.orthonormalBasisOneI.repr.injective (first.trans last.symm)
  subst b
  exact Set.disjoint_left.mp (M.cell_disjoint i j different) ha hb

theorem planarCells_cover : M.planarRegion = ⋃ i, M.planarCells i := by
  rw [planarRegion, M.cover, Set.image_iUnion]
  rfl

/-- Rigid coordinates and boundary-only primitive seams give the exact original intrinsic gap. -/
def planarCellIsometry :
    MetricGluing.Realization (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) ≃ᵢ PolygonalPoint M.region :=
  (MetricGluing.boundaryCoverIsometryEquiv M.planarCells M.planarCells_closed
    M.planarCells_convex M.planarCells_cover).trans
    (PolygonalPoint.affineRegionIsometryEquiv
      Complex.orthonormalBasisOneI.repr.toAffineIsometryEquiv rfl).symm

/-- Every original cell point is fixed physically by the intrinsic gluing identification. -/
@[simp] theorem planarCellIsometry_point_val (i : M.Cell) (p : M.planarCells i) :
    (M.planarCellIsometry (MetricGluing.of (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) i p)).val =
      Complex.orthonormalBasisOneI.repr.symm p.val := rfl

/-- Original internal gap seams are confined to the actual planar cell boundaries. -/
theorem planarCells_seam_boundary (i : M.Cell) (p : M.planarCells i)
    (seam : p ∈ MetricGluing.seamSupport (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) i) : p.val ∉ interior (M.planarCells i) :=
  MetricGluing.distinctCoincident_seamSupport_boundary_of_convex M.planarCells
    M.planarCells_closed M.planarCells_convex M.planarCells_full M.planarCells_disjoint i p seam

/-- Every planar cell representative of an actual bank mark lies on its own cell boundary. -/
theorem planarCell_bank_boundary (side : Bool) (x : {z // z ∈ (M.bank side).carrier})
    (i : M.Cell) (p : M.planarCells i)
    (named : M.planarCellIsometry (MetricGluing.of (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) i p) = M.bankPoint side x) :
    p.val ∉ interior (M.planarCells i) := by
  have position : Complex.orthonormalBasisOneI.repr.symm p.val = x.val :=
    congrArg PolygonalPoint.val named
  have same : p.val = Complex.orthonormalBasisOneI.repr x.val :=
    (Complex.orthonormalBasisOneI.repr.apply_symm_apply p.val).symm.trans
      (congrArg Complex.orthonormalBasisOneI.repr position)
  have boundary : p.val ∈ frontier M.planarRegion := by
    rw [same, planarRegion, ← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_frontier]
    exact ⟨x.val, M.bank_mem_frontier side x, rfl⟩
  intro inside
  exact boundary.2 ((interior_mono
    (MetricGluing.cell_subset_of_cover M.planarCells M.planarCells_cover i)) inside)

/-- Every original closed-edge bank mark has only boundary cell representatives. -/
theorem planarCell_edge_boundary (side : Bool) (k : Fin n) (t : unitInterval)
    (i : M.Cell) (p : M.planarCells i)
    (named : M.planarCellIsometry (MetricGluing.of (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) i p) = M.edgePoint side k t) :
    p.val ∉ interior (M.planarCells i) :=
  M.planarCell_bank_boundary side ⟨(M.bank side).chain.point k t, Or.inl (by
    rw [(M.bank side).chain.path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨k, t, rfl⟩))⟩ i p named

/-- Every original infinite-tail bank mark has only boundary cell representatives. -/
theorem planarCell_tail_boundary (side : Bool) (t : ℝ≥0) (i : M.Cell) (p : M.planarCells i)
    (named : M.planarCellIsometry (MetricGluing.of (fun i => M.planarCells i)
      (MetricGluing.distinctCoincident M.planarCells) i p) = M.tailPoint side t) :
    p.val ∉ interior (M.planarCells i) :=
  M.planarCell_bank_boundary side ⟨(M.bank side).tail t, (M.bank side).tail_mem t⟩ i p named

end Unfoldings.BankGapModel
