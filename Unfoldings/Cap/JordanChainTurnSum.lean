module

public import Unfoldings.Cap.JordanChainCoverage
public import Unfoldings.Cap.RestrictedSectionSum
public import Unfoldings.Geometry.ChainSplit

/-! The actual chain's hinge-error sum is exactly the geometric Jordan bank sum. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

local instance jordanChainSumMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable {n : ℕ}
  (d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n)

local notation "P" => K.projectedBoundaryChain (K.jordanFaces J) d
local notation "Q" => K.jordanContour jordan contains avoids
local notation "R" => C.restrictFaces (K.jordanFaces J)

/-- The actual Jordan contour index of an internal chain vertex. -/
def jordanChainInternalIndex (k : Fin n) : Fin ((Q).length + 1) :=
  ((R).boundaryCycleVertexEquiv Set.univ (Q).cycle (Q).closes (Q).covers).symm
    ((R).boundaryEndAsVertex Set.univ (d.point k.succ))

/-- The index records equality of actual intrinsic vertex copies. -/
theorem jordanChainInternalIndex_vertex (k : Fin n) :
    (R).boundaryEndVertex Set.univ ((Q).cycle.point
        (K.jordanChainInternalIndex jordan contains avoids d k)) =
      (R).boundaryEndVertex Set.univ (d.point k.succ) := by
  exact congrArg Subtype.val
    (((R).boundaryCycleVertexEquiv Set.univ (Q).cycle (Q).closes (Q).covers).apply_symm_apply
      ((R).boundaryEndAsVertex Set.univ (d.point k.succ)))

/-- The named contour position is the literal original chain vertex. -/
theorem jordanChainInternalIndex_position (k : Fin n) :
    K.jordanBankPosition jordan contains avoids
        (K.jordanChainInternalIndex jordan contains avoids d k) =
      (P).vertex k.succ.castSucc := by
  rw [K.projectedBoundaryChain_vertex_castSucc]
  exact congrArg (fun w : (R).Vertex Set.univ =>
    Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).toSpace Set.univ
      ((R).vertexPoint Set.univ w)))
        (K.jordanChainInternalIndex_vertex jordan contains avoids d k)

/-- The weight is the actual one-sided fan error of the same intrinsic vertex copy. -/
theorem jordanChainInternalIndex_turnError (k : Fin n) :
    K.jordanContourTurnError jordan contains avoids
        (K.jordanChainInternalIndex jordan contains avoids d k) =
      K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ) := by
  dsimp only [jordanContourTurnError, restrictedBoundaryTurnError]
  rw [K.jordanChainInternalIndex_vertex]

/-- Original simple-chain internal vertices enumerate exactly the geometric bank indices.
The sum does not assume an ordering or a preselected contour interval. -/
theorem sum_jordan_chain_turnError_eq_geometric_bank
    (injective : Function.Injective (P).vertex) :
    (∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ)) =
      ∑ j ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range (P).path)
        {(P).vertex 0, (P).vertex (Fin.last (n + 1))},
          K.jordanContourTurnError jordan contains avoids j := by
  classical
  refine Finset.sum_bij (fun k _ => K.jordanChainInternalIndex jordan contains avoids d k)
    ?_ ?_ ?_ ?_
  · intro k _member
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [K.jordanChainInternalIndex_position]
      exact (P).vertex_mem_path_range k.succ.castSucc
    · rw [K.jordanChainInternalIndex_position]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro same
        have values := congrArg Fin.val (injective same)
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at values
        omega
      · intro same
        have values := congrArg Fin.val (injective same)
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last] at values
        have bound := k.isLt
        omega
  · intro k _member l _other same
    have positions := congrArg (K.jordanBankPosition jordan contains avoids) same
    rw [K.jordanChainInternalIndex_position, K.jordanChainInternalIndex_position] at positions
    have values := congrArg Fin.val (injective positions)
    apply Fin.ext
    simpa only [Fin.val_castSucc, Fin.val_succ, add_left_inj] using values
  · intro j member
    obtain ⟨k, position⟩ :=
      K.exists_internal_chain_vertex_of_geometric_bank_index jordan contains avoids d j member
    exact ⟨k, Finset.mem_univ _, K.jordanBankPosition_injective jordan contains avoids
      ((K.jordanChainInternalIndex_position jordan contains avoids d k).trans position)⟩
  · intro k _member
    exact (K.jordanChainInternalIndex_turnError jordan contains avoids d k).symm

end Unfoldings.ConvexCap
