module

public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Complex.BoundaryChainTrace
public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.ChainAffineMap

/-! The complete physical polygonal path of an actual original directed boundary chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {n : ℕ}
  (chain : (C.boundarySystem retain).Chain n)

/-- Original spatial starts and the last original endpoint, without normalization. -/
def boundarySpatialChain : PolygonalChain Space (n + 1) :=
  ⟨Fin.lastCases (F.boundaryPosition (C.boundaryTurn retain chain.last))
    (fun i => F.boundaryPosition (chain.point i))⟩

@[simp] theorem boundarySpatialChain_vertex_castSucc (i : Fin (n + 1)) :
    (F.boundarySpatialChain chain).vertex i.castSucc = F.boundaryPosition (chain.point i) := by
  dsimp only [boundarySpatialChain]
  rw [Fin.lastCases_castSucc]

@[simp] theorem boundarySpatialChain_vertex_last :
    (F.boundarySpatialChain chain).vertex (Fin.last (n + 1)) =
      F.boundaryPosition (C.boundaryTurn retain chain.last) := by
  dsimp only [boundarySpatialChain]
  rw [Fin.lastCases_last]

theorem boundarySpatialChain_vertex_succ (i : Fin (n + 1)) :
    (F.boundarySpatialChain chain).vertex i.succ =
      F.boundaryPosition (C.boundaryTurn retain (chain.point i)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, F.boundarySpatialChain_vertex_last]
    rfl
  · rw [Fin.succ_castSucc, F.boundarySpatialChain_vertex_castSucc]
    have next := chain.next j
    change C.boundaryMate retain (C.boundaryTurn retain (chain.point j.castSucc)) =
      chain.point j.succ at next
    rw [← next, F.boundaryPosition_mate]

/-- The whole physical affine bank path retains its original endpoint order. -/
theorem boundarySpatialChain_point (i : Fin (n + 1)) (t : unitInterval) :
    (F.boundarySpatialChain chain).point i t =
      F.toSpace retain (C.directedBoundaryPath (chain.point i) t) := by
  rw [PolygonalChain.point, F.boundarySpatialChain_vertex_castSucc,
    F.boundarySpatialChain_vertex_succ, F.directedBoundaryPath_position,
    F.germDirection_boundary_positions, AffineMap.lineMap_apply_module']
  exact add_comm _ _

/-- Physical chain geometry preserves the full original spatial edge vectors. -/
theorem boundarySpatialChain_edge (i : Fin (n + 1)) :
    (F.boundarySpatialChain chain).edge i = F.germDirection (chain.point i).val := by
  rw [PolygonalChain.edge, F.boundarySpatialChain_vertex_succ,
    F.boundarySpatialChain_vertex_castSucc, F.germDirection_boundary_positions]

/-- The whole physical path has exactly the spatial image of the original intrinsic trace. -/
theorem boundarySpatialChain_path_range :
    Set.range (F.boundarySpatialChain chain).path =
      F.toSpace retain '' C.boundaryChainTrace chain := by
  rw [C.boundaryChainTrace_eq_union_paths]
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    obtain ⟨i, t, same⟩ := (F.boundarySpatialChain chain).path_point_covered (Nat.succ_pos _) u
    exact ⟨C.directedBoundaryPath (chain.point i) t, Set.mem_iUnion.mpr ⟨i, t, rfl⟩,
      (F.boundarySpatialChain_point chain i t).symm.trans same.symm⟩
  · rintro z ⟨x, member, rfl⟩
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp member
    rw [← F.boundarySpatialChain_point chain i t]
    exact (F.boundarySpatialChain chain).path_range.ge (Or.inr (Set.mem_iUnion.mpr ⟨i, t, rfl⟩))

end Unfoldings.SpatialFolding
