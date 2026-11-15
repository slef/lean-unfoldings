module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Cap.JordanContourSegments
public import Unfoldings.Cap.GeometricBankTurnComparison
public import Unfoldings.Geometry.PolygonalVertexCoverage

/-! Actual Jordan bank vertices on a projected chain are exactly its original internal vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

local instance jordanChainCoverageMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable {n : ℕ}
  (d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n)

local notation "P" => K.projectedBoundaryChain (K.jordanFaces J) d
local notation "Q" => K.jordanContour jordan contains avoids

include jordan contains avoids in
/-- An actual Jordan vertex cannot lie inside any one of the chain's actual bank edges. -/
theorem jordanBankPosition_not_mem_open_chain_segment (i : Fin (n + 1))
    (j : Fin ((Q).length + 1)) :
    K.jordanBankPosition jordan contains avoids j ∉ openSegment ℝ
      ((P).vertex i.castSucc) ((P).vertex i.succ) := by
  intro member
  rw [openSegment_eq_image_lineMap] at member
  obtain ⟨t, bounds, equal⟩ := member
  let V := K.jordanFaces J
  let R := C.restrictFaces V
  let w := R.boundaryEndVertex Set.univ ((Q).cycle.point j)
  have projection : K.toRoof.restrictProjection V
      (R.directedBoundaryPath (d.point i) ⟨t, bounds.1.le, bounds.2.le⟩) =
        AffineMap.lineMap ((P).vertex i.castSucc) ((P).vertex i.succ) t := by
    simpa only [PolygonalChain.point] using!
      (K.projectedBoundaryChain_point V d i ⟨t, bounds.1.le, bounds.2.le⟩).symm
  have same : K.toRoof.restrictProjection V
      (R.directedBoundaryPath (d.point i) ⟨t, bounds.1.le, bounds.2.le⟩) =
        K.toRoof.restrictProjection V (R.vertexPoint Set.univ w) := projection.trans equal
  have intrinsic := (K.jordanIntrinsicHomeomorph jordan contains avoids).injective
    (Subtype.ext same)
  exact R.directedBoundaryPath_ne_vertexPoint (d.point i) _ bounds.1 bounds.2 w intrinsic

include jordan contains avoids in
/-- Geometric bank membership supplies an actual internal chain index, without assuming
that a contour enumeration or subdivision has already been matched. -/
theorem exists_internal_chain_vertex_of_geometric_bank_index
    (j : Fin ((Q).length + 1))
    (member : j ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range (P).path)
      {(P).vertex 0, (P).vertex (Fin.last (n + 1))}) :
    ∃ k : Fin n, (P).vertex k.succ.castSucc = K.jordanBankPosition jordan contains avoids j := by
  obtain ⟨on_path, not_end⟩ := (Finset.mem_filter.mp member).2
  apply (P).exists_internal_vertex_of_mem_path_of_not_open _ on_path
  · intro same
    exact not_end (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl same)
  · intro same
    exact not_end (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr same)
  · intro i
    exact K.jordanBankPosition_not_mem_open_chain_segment jordan contains avoids d i j

end Unfoldings.ConvexCap
