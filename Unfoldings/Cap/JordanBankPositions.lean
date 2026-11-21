module

public import Unfoldings.Cap.BoundarySectionConstruction
public import Unfoldings.Cap.JordanContourTurns

/-! Literal planar positions of actual ordered Jordan boundary vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- Actual projected bank positions, with no rolling or development coordinates. -/
def jordanBankPosition (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : Plane :=
  Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
    ((K.jordanContour jordan contains avoids).cycle.point i))

include jordan contains avoids in
open Classical in
theorem jordanBankPosition_eq_projectedVertex
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanBankPosition jordan contains avoids i =
      K.projectedVertex ((K.jordanContourVertexEquiv jordan contains avoids) i).val := by
  exact (K.projected_restricted_boundaryPosition (K.jordanFaces J)
    ((K.jordanContour jordan contains avoids).cycle.point i)).symm

include jordan contains avoids in
open Classical in
theorem jordanBankPosition_mem_curve
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanBankPosition jordan contains avoids i ∈ J := by
  let R := C.restrictFaces (K.jordanFaces J)
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  have member := (K.jordan_isBoundaryVertex_iff jordan contains avoids
    (R.boundaryEndVertex Set.univ p)).mp (R.boundaryEndAsVertex Set.univ p).property
  rw [K.projected_restricted_boundaryPosition] at member
  exact member

include jordan contains avoids in
open Classical in
theorem jordanBankPosition_injective :
    Function.Injective (K.jordanBankPosition jordan contains avoids) := by
  intro i j same
  apply (K.jordanContourVertexEquiv jordan contains avoids).injective
  apply Subtype.ext
  apply K.projectedVertex_injective
  change K.projectedVertex (C.includeRestrictedVertexUniv (K.jordanFaces J)
      ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ
        ((K.jordanContour jordan contains avoids).cycle.point i))) =
    K.projectedVertex (C.includeRestrictedVertexUniv (K.jordanFaces J)
      ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ
        ((K.jordanContour jordan contains avoids).cycle.point j)))
  rw [K.projected_restricted_boundaryPosition, K.projected_restricted_boundaryPosition]
  exact same

include jordan contains avoids in
open Classical in
/-- A finite geometric corner set is counted once, independently of triangle valence. -/
theorem card_jordanBankPosition_preimage_le (corners : Finset Plane) :
    (Finset.univ.filter (fun i => K.jordanBankPosition jordan contains avoids i ∈ corners)).card ≤
      corners.card := by
  classical
  apply Finset.card_le_card_of_injOn (K.jordanBankPosition jordan contains avoids)
  · intro i member
    exact (Finset.mem_filter.mp member).2
  · exact (K.jordanBankPosition_injective jordan contains avoids).injOn

end Unfoldings.ConvexCap
