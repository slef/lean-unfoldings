module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Geometry.ChainSplit

/-! Distinct actual path hinges charge each original cap vertex curvature at most once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance originalChainCurvatureMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- The actual starting bank copy projects to its original vertex class. -/
theorem original_chain_vertex_projected_position (i : Fin (n + 1)) :
    K.projectedVertex
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1) =
      (K.projectedBoundaryChain U c).vertex i.castSucc := by
  rw [K.projectedVertex_ofCorner, K.projectedBoundaryChain_vertex_castSucc,
    SpatialFolding.boundaryPosition_raw]
  rfl

/-- A physical path strictly inside the cap uses only original interior vertex stars. -/
theorem original_chain_vertex_internal_of_path_subset
    (inside : Set.range (K.projectedBoundaryChain U c).path ⊆ interior K.footprint)
    (i : Fin (n + 1)) : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1) := by
  apply (K.projectedVertex_mem_interior_iff _).mp
  rw [K.original_chain_vertex_projected_position]
  exact inside ((K.projectedBoundaryChain U c).vertex_mem_path_range i.castSucc)

/-- Physical path simplicity derives injectivity of the original internal vertex classes. -/
theorem original_chain_internal_vertex_injective
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex) :
    Function.Injective (fun k : Fin n =>
      C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) := by
  intro k l same
  have projected := congrArg K.projectedVertex same
  have position (i : Fin (n + 1)) : K.projectedVertex
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1) =
      (K.projectedBoundaryChain U c).vertex i.castSucc := by
    rw [K.projectedVertex_ofCorner, K.projectedBoundaryChain_vertex_castSucc,
      SpatialFolding.boundaryPosition_raw]
    rfl
  rw [position, position] at projected
  apply Fin.succ_injective
  apply Fin.castSucc_injective
  exact simple projected

/-- No combinatorial or valence factor enters the actual original hinge-curvature budget. -/
theorem sum_original_chain_internal_curvature_le_total
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex) :
    (∑ k : Fin n, C.interiorAngularDefect Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1)) ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  have bound := K.sum_interiorAngularDefect_le_totalCurvature (Finset.univ.image
    (fun k : Fin n => C.vertexOfCorner Set.univ
      (C.includeRestrictedGerm U (c.point k.succ).val).1))
  rw [Finset.sum_image (fun _ _ _ _ same =>
    K.original_chain_internal_vertex_injective U c simple same)] at bound
  exact bound

end Unfoldings.ConvexCap
