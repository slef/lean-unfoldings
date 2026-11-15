module

public import Unfoldings.Cap.ProjectedBoundaryChainAgreement
public import Unfoldings.Roof.CapBridge

/-! Actual original banks lift to an embedded face patch in their intrinsic boundary order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance chainLiftMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}

/-- An actual target bank with the same raw original germ is enough to lift a full chain.
Target vertex injectivity derives the actual boundary successor, rather than assuming a
fan, contour-index or adjacency correspondence. -/
theorem exists_restricted_boundary_chain_of_original_banks
    (embedded : Function.Injective (fun w : (C.restrictFaces V).Vertex rightRetain =>
      Cap.horizontal ((K.folding.restrictFaces V).toSpace rightRetain
        ((C.restrictFaces V).vertexPoint rightRetain w))))
    (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
    (available : ∀ i, ∃ q : (C.restrictFaces V).BoundaryEnd rightRetain,
      C.includeRestrictedGerm V q.val = C.includeRestrictedGerm U (c.point i).val) :
    ∃ d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n,
      ∀ i, C.includeRestrictedGerm V (d.point i).val =
        C.includeRestrictedGerm U (c.point i).val := by
  let R := C.restrictFaces U
  let T := C.restrictFaces V
  let F := K.folding.restrictFaces U
  let G := K.folding.restrictFaces V
  choose point banks using available
  have turn_banks (i) : C.includeRestrictedGerm V (T.boundaryTurn rightRetain (point i)).val =
      C.includeRestrictedGerm U (R.boundaryTurn leftRetain (c.point i)).val := by
    rw [C.includeRestrictedGerm_boundaryTurn, C.includeRestrictedGerm_boundaryTurn]
    simpa only using! congrArg
      (fun p : C.Germ => C.germOfEndpoint (C.germEdge p) (!p.2)) (banks i)
  have injective : Function.Injective point := by
    intro i j equal
    apply c.injective
    apply Subtype.ext
    apply C.includeRestrictedGerm_injective U
    exact (banks i).symm.trans ((congrArg (fun p : T.BoundaryEnd rightRetain =>
      C.includeRestrictedGerm V p.val) equal).trans (banks j))
  have disjoint (i j) : point i ≠ T.boundaryTurn rightRetain (point j) := by
    intro equal
    apply c.disjoint i j
    apply Subtype.ext
    apply C.includeRestrictedGerm_injective U
    exact (banks i).symm.trans ((congrArg (fun p : T.BoundaryEnd rightRetain =>
      C.includeRestrictedGerm V p.val) equal).trans (turn_banks j))
  have positions (i) : Cap.horizontal (G.boundaryPosition (point i)) =
      Cap.horizontal (F.boundaryPosition (c.point i)) := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! congrArg
      (fun p : C.Germ => Cap.horizontal (K.folding.place p.1.1
        ((C.triangle p.1.1).vertex p.1.2))) (banks i)
  have turn_positions (i) : Cap.horizontal (G.boundaryPosition
        (T.boundaryTurn rightRetain (point i))) =
      Cap.horizontal (F.boundaryPosition (R.boundaryTurn leftRetain (c.point i))) := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! congrArg
      (fun p : C.Germ => Cap.horizontal (K.folding.place p.1.1
        ((C.triangle p.1.1).vertex p.1.2))) (turn_banks i)
  have next (i : Fin n) : T.boundaryMate rightRetain
      (T.boundaryTurn rightRetain (point i.castSucc)) = point i.succ := by
    have same : T.boundaryEndVertex rightRetain (point i.succ) =
        T.boundaryEndVertex rightRetain (T.boundaryTurn rightRetain (point i.castSucc)) := by
      apply embedded
      change Cap.horizontal (G.boundaryPosition (point i.succ)) =
        Cap.horizontal (G.boundaryPosition (T.boundaryTurn rightRetain (point i.castSucc)))
      rw [positions, turn_positions]
      have step : R.boundaryMate leftRetain (R.boundaryTurn leftRetain (c.point i.castSucc)) =
          c.point i.succ := c.next i
      rw [← step, F.boundaryPosition_mate]
    exact ((T.exists_unique_other_boundaryEnd rightRetain
      (T.boundaryTurn rightRetain (point i.castSucc))).unique
        ⟨disjoint i.succ i.castSucc, same⟩
        (T.boundaryMate_spec rightRetain _)).symm
  exact ⟨⟨point, injective, disjoint, next⟩, banks⟩

end Unfoldings.ConvexCap
