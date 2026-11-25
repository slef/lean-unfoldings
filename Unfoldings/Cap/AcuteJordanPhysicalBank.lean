module

public import Unfoldings.Cap.JordanPhysicalChainLift
public import Unfoldings.Cap.JordanChainTurnSum
public import Unfoldings.Cap.PhysicalBankSideDichotomy
public import Unfoldings.Cap.OriginalChainTurnError
public import Unfoldings.Geometry.AcuteChainExterior

/-! Recover the actual original one-sided bank from the appropriate two-link closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance acutePhysicalBankMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (apex : Plane)

local notation "Path" => K.projectedBoundaryChain U chain
local notation "Curve" => PolygonalChain.twoLinkClosure (K.projectedBoundaryChain U chain) apex

/-- A closure avoiding the opposite initial face follows the original cut bank
through every subsequent hinge, including on intermediate flat seams. -/
theorem exists_acute_jordan_chain_on_original_bank
    (h k : Plane →L[ℝ] ℝ)
    (first : ∀ i : Fin (n + 1), 0 < h ((Path).edge i))
    (last : ∀ i : Fin (n + 1), 0 < k ((Path).edge i))
    (initial : h apex ≤ h ((Path).vertex 0))
    (terminal : k ((Path).vertex (Fin.last (n + 1))) ≤ k apex)
    (jordan : Schoenflies.IsJordanCurve Curve) (inside : Curve ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) Curve)
    (outside : (C.mateGerm Set.univ (C.includeRestrictedGerm U chain.first.val)).1.1 ∉
      K.jordanFaces Curve) :
    ∃ d : ((C.restrictFaces (K.jordanFaces Curve)).boundarySystem Set.univ).Chain n,
      (∀ i, C.includeRestrictedGerm (K.jordanFaces Curve) (d.point i).val =
        C.includeRestrictedGerm U (chain.point i).val) ∧
      K.projectedBoundaryChain (K.jordanFaces Curve) d = (Path) := by
  let P := Path
  let J := Curve
  let V := K.jordanFaces J
  have injective := (P.strictMono_linear_vertices h first).injective
  have simple : Function.Injective P.vertex := fun _ _ same => injective (congrArg h same)
  have internal (i : Fin (n + 1)) : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (chain.point i).val).1) := by
    apply (K.projectedVertex_mem_interior_iff _).mp
    have position : K.projectedVertex
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (chain.point i).val).1) =
      P.vertex i.castSucc := by
      rw [K.projectedVertex_ofCorner, K.projectedBoundaryChain_vertex_castSucc,
        SpatialFolding.boundaryPosition_raw]
      rfl
    rw [position]
    exact inside (Or.inl (P.vertex_mem_path_range i.castSucc))
  obtain ⟨d, positions, vectors⟩ := K.exists_jordan_physical_chain_of_local_rays jordan
    (inside.trans interior_subset) avoids U chain simple internal
    (fun _ member => Or.inl (K.projectedBoundaryChain_original_edge_subset U chain 0 member))
    (by
      intro i
      have near := P.eventually_mem_twoLinkClosure_iff_internal_rays apex h k
        first last initial terminal i
      have rays := K.projectedBoundaryChain_internal_rays U chain i
      rw [← K.projectedBoundaryChain_vertex_castSucc U chain i.succ, rays.1, rays.2, Set.union_comm]
      exact near.mono (fun _ model => model.mp))
  rcases K.restricted_physical_boundary_chain_bank_dichotomy U chain V d positions vectors internal
    with same | opposite
  · exact ⟨d, same, (K.projectedBoundaryChain_eq_of_original_banks U V chain d
      (fun i => (same i).symm)).symm⟩
  · have excluded := congrArg (fun germ : C.Germ => germ.1.1) (opposite 0)
    exact (outside (excluded ▸ d.first.val.1.1.property)).elim

end Unfoldings.ConvexCap
