module

public import Unfoldings.Cap.BoundarySectionTrace
public import Unfoldings.Complex.BoundaryContour

/-! Construct physical boundary section traces from literal projected bank coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Projected restricted bank positions keep the exact original geometric vertex. -/
theorem projected_restricted_boundaryPosition (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    K.projectedVertex (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) := by
  change K.projectedVertex (C.vertexOfCorner Set.univ (p.val.1.1.val, p.val.1.2)) = _
  rw [K.projectedVertex_ofCorner, (K.folding.restrictFaces U).boundaryPosition_raw]
  rfl

open Classical in
/-- Every restricted physical bank vertex is on the actual original roof graph. -/
theorem restricted_boundaryPosition_eq_graph (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    (K.folding.restrictFaces U).boundaryPosition p =
      Cap.horizontalAtHeight (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p))
        (K.roofHeight (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p))) := by
  let z := (K.folding.restrictFaces U).boundaryPosition p
  have present : z ∈ K.folding.surface := by
    change (K.folding.restrictFaces U).boundaryPosition p ∈ K.folding.surface
    rw [(K.folding.restrictFaces U).boundaryPosition_raw]
    exact Set.mem_iUnion.mpr ⟨p.val.1.1.val,
      ⟨(C.triangle p.val.1.1.val).vertex p.val.1.2,
        (C.triangle p.val.1.1.val).vertex_mem p.val.1.2, rfl⟩⟩
  have height := ((K.surface_iff_roofHeight z).mp present).2
  change z = Cap.horizontalAtHeight (Cap.horizontal z) (K.roofHeight (Cap.horizontal z))
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact height

namespace BoundarySectionTrace

variable {K}

open Classical in
/-- Only the actual projected coordinates and directed boundary adjacency are supplied. -/
def ofProjected {U : Set Face} (origin direction : Plane) (turns : ℕ)
    (bank : Fin (turns + 2) → (C.restrictFaces U).BoundaryEnd Set.univ)
    (next : ∀ i : Fin (turns + 1), (C.restrictFaces U).boundaryMate Set.univ
      ((C.restrictFaces U).boundaryTurn Set.univ (bank i.castSucc)) = bank i.succ)
    (time : Fin (turns + 2) → ℝ) (increasing : StrictMono time)
    (projection : ∀ i, Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (bank i)) =
      origin + time i • direction) : K.BoundarySectionTrace U origin direction where
  turns := turns
  bank := bank
  next := next
  time := time
  increasing := increasing
  position i := by
    have graph := K.restricted_boundaryPosition_eq_graph U (bank i)
    rw [projection] at graph
    exact graph

open Classical in
/-- A literal contiguous straight portion of the actual contour supplies the section trace. -/
def ofContourInterval {U : Set Face} (origin direction : Plane)
    (Q : (C.restrictFaces U).BoundaryContour Set.univ) (first turns : ℕ)
    (fits : first + turns + 1 ≤ Q.length)
    (time : Fin (turns + 2) → ℝ) (increasing : StrictMono time)
    (projection : ∀ i : Fin (turns + 2),
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        (Q.cycle.point ⟨first + i.val, by omega⟩)) = origin + time i • direction) :
    K.BoundarySectionTrace U origin direction :=
  ofProjected origin direction turns (fun i => Q.cycle.point ⟨first + i.val, by omega⟩)
    (fun i => Q.cycle.next ⟨first + i.val, by omega⟩) time increasing projection

variable {U : Set Face} {origin direction : Plane} (T : K.BoundarySectionTrace U origin direction)

open Classical in
/-- Literal containment in the footprint interior derives the original vertex-interiority test. -/
theorem original_interior (inside : ∀ i, origin + T.time i • direction ∈ interior K.footprint)
    (i : Fin (T.turns + 2)) :
    ¬ C.IsBoundaryVertex Set.univ (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ (T.bank i))) := by
  apply (K.projectedVertex_mem_interior_iff _).mp
  rw [K.projected_restricted_boundaryPosition U, T.position]
  simpa only [ConvexCap.roofSectionPoint, Cap.horizontal_horizontalAtHeight] using inside i

open Classical in
/-- A physical straight boundary section inside the footprint has total fan error at most 2φ. -/
theorem sum_abs_turnError_le_tilt_of_interior (unit : ‖direction‖ = 1)
    (inside : ∀ i, origin + T.time i • direction ∈ interior K.footprint)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i, |T.turnError i|) ≤ 2 * φ :=
  T.sum_abs_turnError_le_tilt unit (fun i => T.original_interior inside i.castSucc.succ)
    nonnegative small tilt

end BoundarySectionTrace
end Unfoldings.ConvexCap
