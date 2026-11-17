module

public import Unfoldings.Polyhedron.BoundaryChainGeometry
public import Unfoldings.Polyhedron.DirectedBankSubinterval
public import Unfoldings.Geometry.ChainPaths

/-! Exact horizontal polygonal paths of actual spatially folded boundary chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {n : ℕ}
  (chain : (C.boundarySystem retain).Chain n)

/-- Project every actual bank start and the true final endpoint into the horizontal plane. -/
def projectedBoundaryChain : PolygonalChain Plane (n + 1) :=
  (F.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap

@[simp] theorem projectedBoundaryChain_vertex_castSucc (i : Fin (n + 1)) :
    (F.projectedBoundaryChain chain).vertex i.castSucc =
      Cap.horizontal (F.boundaryPosition (chain.point i)) := by
  exact congrArg Cap.horizontal (F.boundarySpatialChain_vertex_castSucc chain i)

@[simp] theorem projectedBoundaryChain_vertex_succ (i : Fin (n + 1)) :
    (F.projectedBoundaryChain chain).vertex i.succ =
      Cap.horizontal (F.boundaryPosition (C.boundaryTurn retain (chain.point i))) := by
  exact congrArg Cap.horizontal (F.boundarySpatialChain_vertex_succ chain i)

@[simp] theorem projectedBoundaryChain_vertex_last :
    (F.projectedBoundaryChain chain).vertex (Fin.last (n + 1)) =
      Cap.horizontal (F.boundaryPosition (C.boundaryTurn retain chain.last)) := by
  exact congrArg Cap.horizontal (F.boundarySpatialChain_vertex_last chain)

/-- The entire physical projected edge retains its actual directed spatial bank vector. -/
theorem projectedBoundaryChain_edge (i : Fin (n + 1)) :
    (F.projectedBoundaryChain chain).edge i =
      Cap.horizontal (F.germDirection (chain.point i).val) := by
  rw [PolygonalChain.edge, F.projectedBoundaryChain_vertex_succ,
    F.projectedBoundaryChain_vertex_castSucc, F.germDirection_boundary_positions, map_sub]

/-- Every point keeps its original directed bank parameter, including both endpoints. -/
theorem projectedBoundaryChain_point (i : Fin (n + 1)) (t : unitInterval) :
    (F.projectedBoundaryChain chain).point i t =
      Cap.horizontal (F.toSpace retain (C.directedBoundaryPath (chain.point i) t)) := by
  rw [PolygonalChain.point, F.projectedBoundaryChain_vertex_castSucc,
    F.projectedBoundaryChain_vertex_succ, F.directedBoundaryPath_lineMap]
  exact (Cap.horizontal.toAffineMap.apply_lineMap _ _ _).symm

/-- The complete polygonal path is precisely the horizontal image of the intrinsic trace. -/
theorem projectedBoundaryChain_path_range :
    Set.range (F.projectedBoundaryChain chain).path =
      (Cap.horizontal ∘ F.toSpace retain) '' C.boundaryChainTrace chain := by
  ext z
  rw [C.boundaryChainTrace_eq_union_paths]
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, t, same⟩ := (F.projectedBoundaryChain chain).path_point_covered (by omega) s
    refine ⟨C.directedBoundaryPath (chain.point i) t,
      Set.mem_iUnion.mpr ⟨i, t, rfl⟩, ?_⟩
    exact (F.projectedBoundaryChain_point chain i t).symm.trans same.symm
  · rintro ⟨x, member, at_z⟩
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp member
    rw [(F.projectedBoundaryChain chain).path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, t,
      (F.projectedBoundaryChain_point chain i t).trans at_z⟩)

end Unfoldings.SpatialFolding
