module

public import Unfoldings.Cap.ProjectedRawBankRays
public import Unfoldings.Complex.BoundaryChainRolling
public import Unfoldings.Complex.BoundaryContourPaths
public import Unfoldings.Geometry.ChainPaths

/-! The complete physical projected polygonal chain of actual directed original banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance projectedBoundaryChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- All actual bank starting points followed by the true far endpoint of the final bank. -/
def projectedBoundaryChain : PolygonalChain Plane (n + 1) where
  vertex := Fin.lastCases
    (Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
      ((C.restrictFaces U).boundaryTurn retain c.last)))
    (fun i => Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (c.point i)))

@[simp] theorem projectedBoundaryChain_vertex_castSucc (i : Fin (n + 1)) :
    (K.projectedBoundaryChain U c).vertex i.castSucc =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition (c.point i)) := by
  simp only [projectedBoundaryChain, Fin.lastCases_castSucc]

@[simp] theorem projectedBoundaryChain_vertex_last :
    (K.projectedBoundaryChain U c).vertex (Fin.last (n + 1)) =
      Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition
        ((C.restrictFaces U).boundaryTurn retain c.last)) := by
  simp only [projectedBoundaryChain, Fin.lastCases_last]

/-- Each entire projected edge is its actual folded bank direction, including the final edge. -/
theorem projectedBoundaryChain_edge (i : Fin (n + 1)) :
    (K.projectedBoundaryChain U c).edge i =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection (c.point i).val) := by
  let F := K.folding.restrictFaces U
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [PolygonalChain.edge, Fin.succ_last, K.projectedBoundaryChain_vertex_last,
      K.projectedBoundaryChain_vertex_castSucc, F.germDirection_boundary_positions, map_sub]
    rfl
  · rw [PolygonalChain.edge, Fin.succ_castSucc, K.projectedBoundaryChain_vertex_castSucc,
      K.projectedBoundaryChain_vertex_castSucc, F.germDirection_boundary_step (c.next k), map_sub]

/-- No physical projected bank disappears, even at flat inserted vertices. -/
theorem projectedBoundaryChain_edge_ne_zero (i : Fin (n + 1)) :
    (K.projectedBoundaryChain U c).edge i ≠ 0 := by
  rw [K.projectedBoundaryChain_edge]
  let raw := C.includeRestrictedGerm U (c.point i).val
  let p : C.LinkGerm Set.univ (C.vertexOfCorner Set.univ raw.1) := ⟨raw, rfl⟩
  have genuine := K.projectedGermRay_ne_zero p
  rw [← K.horizontal_germDirection] at genuine
  simpa only using! genuine

/-- Exact physical parametrization of every directed bank, including its endpoints. -/
theorem projectedBoundaryChain_point (i : Fin (n + 1)) (t : unitInterval) :
    (K.projectedBoundaryChain U c).point i t =
      Cap.horizontal ((K.folding.restrictFaces U).toSpace retain
        ((C.restrictFaces U).directedBoundaryPath (c.point i) t)) := by
  rw [PolygonalChain.point, AffineMap.lineMap_apply_module',
    ← PolygonalChain.edge, K.projectedBoundaryChain_edge,
    K.projectedBoundaryChain_vertex_castSucc,
    (K.folding.restrictFaces U).directedBoundaryPath_position, map_add, map_smul]
  exact add_comm _ _

/-- The two physical hinge directions are the original neighboring projected chain rays. -/
theorem projectedBoundaryChain_internal_rays (i : Fin n) :
    Cap.horizontal ((K.folding.restrictFaces U).germDirection (c.point i.succ).val) =
        (K.projectedBoundaryChain U c).vertex i.succ.succ -
          (K.projectedBoundaryChain U c).vertex i.succ.castSucc ∧
      Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate retain (c.point i.succ)).val) =
        (K.projectedBoundaryChain U c).vertex i.castSucc.castSucc -
          (K.projectedBoundaryChain U c).vertex i.succ.castSucc := by
  refine ⟨(K.projectedBoundaryChain_edge U c i.succ).symm, ?_⟩
  rw [(K.folding.restrictFaces U).germDirection_boundary_incoming (c.next i), map_sub,
    K.projectedBoundaryChain_vertex_castSucc, K.projectedBoundaryChain_vertex_castSucc]

/-- Every original projected bank edge is wholly present in the actual projected path. -/
theorem projectedBoundaryChain_original_edge_subset (i : Fin (n + 1)) :
    (K.projectedTriangle (c.point i).val.1.1.val).edge
        (C.germEdge (C.includeRestrictedGerm U (c.point i).val)).edge ⊆
      Set.range (K.projectedBoundaryChain U c).path := by
  intro z member
  rw [ConvexCap.projectedTriangle, Triangle.affineImage_edge] at member
  obtain ⟨x, on_edge, equal⟩ := member
  let R := C.restrictFaces U
  let bank := (R.boundaryEndEquiv retain (c.point i)).1
  let y : (R.triangle bank.val.face).Edge bank.val.edge := ⟨x, on_edge⟩
  obtain ⟨t, parameter⟩ := R.bankParameterFromEnd_surjective bank
    (R.boundaryEndEquiv retain (c.point i)).2 y
  have at_point : (K.projectedBoundaryChain U c).point i t = z := by
    rw [K.projectedBoundaryChain_point]
    change Cap.horizontal ((K.folding.restrictFaces U).toSpace retain
      (R.bankMap retain bank (R.bankParameterFromEnd bank
        (R.boundaryEndEquiv retain (c.point i)).2 t))) = z
    rw [parameter]
    exact equal
  rw [(K.projectedBoundaryChain U c).path_range]
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, t, at_point⟩)

end Unfoldings.ConvexCap
