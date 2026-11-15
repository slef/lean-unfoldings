module

public import Unfoldings.Cap.JordanPhysicalChainLift
public import Unfoldings.Geometry.RadialClosureVertexRays
public import Unfoldings.Geometry.PolygonalVertexRays

/-! Source-radial geometry constructs the actual physical Jordan traversal without a side input. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance radialPhysicalChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n) (source closing : Plane)

local notation "P" => K.projectedBoundaryChain U c
local notation "J" => PolygonalChain.threeSegmentClosure
  (K.projectedBoundaryChain U c) source closing

/-- Actual radial geometry constructs every Jordan bank, full spatial vector and the exact
projected path. Initial incident-side, sign and nonrim-bank certificates are all derived.
The intrinsic selected fan can still be the prescribed bank's complementary original side. -/
theorem exists_radial_jordan_physical_chain
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J) :
    ∃ d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n,
      (∀ i, (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition (d.point i) =
        (K.folding.restrictFaces U).boundaryPosition (c.point i)) ∧
      (∀ i, (K.folding.restrictFaces (K.jordanFaces J)).germDirection (d.point i).val =
        (K.folding.restrictFaces U).germDirection (c.point i).val) ∧
      K.projectedBoundaryChain (K.jordanFaces J) d = (P) := by
  have strict := (P).vertex_radius_strictMono_of_radial source radial
    (K.projectedBoundaryChain_edge_ne_zero U c)
  have simple : Function.Injective (P).vertex := fun _ _ same =>
    strict.injective (congrArg (dist source) same)
  have internal (i : Fin (n + 1)) : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1) := by
    apply (K.projectedVertex_mem_interior_iff _).mp
    have position : K.projectedVertex
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1) =
      (P).vertex i.castSucc := by
      rw [K.projectedVertex_ofCorner, K.projectedBoundaryChain_vertex_castSucc,
        SpatialFolding.boundaryPosition_raw]
      rfl
    rw [position]
    exact inside (Or.inl ((P).vertex_mem_path_range i.castSucc))
  obtain ⟨d, positions, vectors⟩ := K.exists_jordan_physical_chain_of_local_rays jordan
    (inside.trans interior_subset) avoids U c simple internal
    (fun _ member => Or.inl (K.projectedBoundaryChain_original_edge_subset U c 0 member))
    (by
      intro i
      have near := (P).eventually_mem_radialClosure_iff_internal_rays source closing radial
        (K.projectedBoundaryChain_edge_ne_zero U c) initial height supported excluded outward i
      have rays := K.projectedBoundaryChain_internal_rays U c i
      rw [← K.projectedBoundaryChain_vertex_castSucc U c i.succ, rays.1, rays.2, Set.union_comm]
      filter_upwards [near] with z model member
      exact model.mp member)
  exact ⟨d, positions, vectors,
    K.projectedBoundaryChain_eq_of_physical_bank_geometry U (K.jordanFaces J) c d positions vectors⟩

end Unfoldings.ConvexCap
