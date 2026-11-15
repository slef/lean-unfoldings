module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Cap.SignedJordanLocalChainLift
public import Unfoldings.Geometry.RadialClosureVertexRays

/-! Actual source-radial banks construct their Jordan comparison without fan certificates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance signedRadialJordanChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (source closing : Plane)

local notation "P" => K.projectedBoundaryChain U chain

/-- Genuine physical radial geometry and one initial incident side construct the actual
Jordan comparison chain. All later original fans, lengths, real heading prefixes and
full roll agree. No orientation, local ray, fan-angle or contour-matching
certificate is supplied. -/
theorem exists_radial_jordan_boundary_chain_signed
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve ((P).threeSegmentClosure source closing))
    (contains : (P).threeSegmentClosure source closing ⊆ K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier)
      ((P).threeSegmentClosure source closing))
    (selected : chain.first.val.1.1.val ∈ K.jordanFaces ((P).threeSegmentClosure source closing)) :
    ∃ d : ((C.restrictFaces (K.jordanFaces ((P).threeSegmentClosure source closing))).boundarySystem
        Set.univ).Chain n,
      (∀ i, C.includeRestrictedGerm (K.jordanFaces ((P).threeSegmentClosure source closing))
        (d.point i).val = C.includeRestrictedGerm U (chain.point i).val) ∧
      (∀ i, (C.restrictFaces
        (K.jordanFaces ((P).threeSegmentClosure source closing))).boundaryChainRollHeading d i =
          (C.restrictFaces U).boundaryChainRollHeading chain i) ∧
      (C.restrictFaces (K.jordanFaces ((P).threeSegmentClosure source closing))).boundaryChainRoll
        d = (C.restrictFaces U).boundaryChainRoll chain := by
  apply K.exists_jordan_boundary_chain_of_local_rays_signed jordan contains avoids U chain
    selected
  · intro z member
    exact Or.inl (K.projectedBoundaryChain_original_edge_subset U chain 0 member)
  · intro i
    have near := (P).eventually_mem_radialClosure_iff_internal_rays source closing radial
      (K.projectedBoundaryChain_edge_ne_zero U chain) initial height supported excluded outward i
    have rays := K.projectedBoundaryChain_internal_rays U chain i
    rw [← K.projectedBoundaryChain_vertex_castSucc U chain i.succ, rays.1, rays.2,
      Set.union_comm]
    filter_upwards [near] with z model member
    exact model.mp member

end Unfoldings.ConvexCap
