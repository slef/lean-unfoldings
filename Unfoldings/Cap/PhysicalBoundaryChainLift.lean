module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Polyhedron.BankLengths

/-! Construct actual target bank chains from exact physical positions and full edge vectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance physicalChainLiftMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)

/-- Physical matching banks construct their actual target successor order. Original face
labels may change to the opposite incident side; no fan or heading match is assumed. -/
theorem exists_restricted_boundary_chain_of_physical_banks
    (embedded : Function.Injective (fun w : (C.restrictFaces V).Vertex rightRetain =>
      Cap.horizontal ((K.folding.restrictFaces V).toSpace rightRetain
        ((C.restrictFaces V).vertexPoint rightRetain w))))
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex)
    (available : ∀ i, ∃ q : (C.restrictFaces V).BoundaryEnd rightRetain,
      (K.folding.restrictFaces V).boundaryPosition q =
          (K.folding.restrictFaces U).boundaryPosition (c.point i) ∧
        (K.folding.restrictFaces V).germDirection q.val =
          (K.folding.restrictFaces U).germDirection (c.point i).val) :
    ∃ d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n,
      (∀ i, (K.folding.restrictFaces V).boundaryPosition (d.point i) =
        (K.folding.restrictFaces U).boundaryPosition (c.point i)) ∧
      ∀ i, (K.folding.restrictFaces V).germDirection (d.point i).val =
        (K.folding.restrictFaces U).germDirection (c.point i).val := by
  let T := C.restrictFaces V
  let G := K.folding.restrictFaces V
  let P := K.projectedBoundaryChain U c
  choose point positions vectors using available
  have starts (i) : Cap.horizontal (G.boundaryPosition (point i)) = P.vertex i.castSucc := by
    rw [positions, K.projectedBoundaryChain_vertex_castSucc]
  have ends (i) : Cap.horizontal (G.boundaryPosition (T.boundaryTurn rightRetain (point i))) =
      P.vertex i.succ := by
    calc
      _ = Cap.horizontal (G.boundaryPosition (point i)) +
          Cap.horizontal (G.germDirection (point i).val) := by
        rw [G.germDirection_boundary_positions, map_sub]
        abel
      _ = P.vertex i.castSucc + P.edge i := by
        rw [starts, vectors, K.projectedBoundaryChain_edge]
      _ = _ := by rw [PolygonalChain.edge]; abel
  have injective : Function.Injective point := by
    intro i j same
    apply Fin.castSucc_injective
    apply simple
    rw [← starts, ← starts, same]
  have disjoint (i j) : point i ≠ T.boundaryTurn rightRetain (point j) := by
    intro same
    have first : i.castSucc = j.succ := simple (by rw [← starts, ← ends, same])
    have last : i.succ = j.castSucc := simple (by
      rw [← ends, ← starts, same, T.boundaryTurn_involutive])
    have left := congrArg Fin.val first
    have right := congrArg Fin.val last
    simp only [Fin.val_castSucc, Fin.val_succ] at left right
    omega
  have next (i : Fin n) : T.boundaryMate rightRetain
      (T.boundaryTurn rightRetain (point i.castSucc)) = point i.succ := by
    have same : T.boundaryEndVertex rightRetain (point i.succ) =
        T.boundaryEndVertex rightRetain (T.boundaryTurn rightRetain (point i.castSucc)) := by
      apply embedded
      change Cap.horizontal (G.boundaryPosition (point i.succ)) =
        Cap.horizontal (G.boundaryPosition (T.boundaryTurn rightRetain (point i.castSucc)))
      rw [starts, ends, Fin.succ_castSucc]
    exact ((T.exists_unique_other_boundaryEnd rightRetain
      (T.boundaryTurn rightRetain (point i.castSucc))).unique
        ⟨disjoint i.succ i.castSucc, same⟩ (T.boundaryMate_spec rightRetain _)).symm
  exact ⟨⟨point, injective, disjoint, next⟩, positions, vectors⟩


/-- Physical bank positions and full vectors preserve the entire projected chain,
including the true terminal endpoint. Incident original faces may differ. -/
theorem projectedBoundaryChain_eq_of_physical_bank_geometry
    (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
    (positions : ∀ i, (K.folding.restrictFaces V).boundaryPosition (d.point i) =
      (K.folding.restrictFaces U).boundaryPosition (c.point i))
    (vectors : ∀ i, (K.folding.restrictFaces V).germDirection (d.point i).val =
      (K.folding.restrictFaces U).germDirection (c.point i).val) :
    K.projectedBoundaryChain V d = K.projectedBoundaryChain U c := by
  let R := C.restrictFaces U
  let T := C.restrictFaces V
  let F := K.folding.restrictFaces U
  let G := K.folding.restrictFaces V
  have endpoint : G.boundaryPosition (T.boundaryTurn rightRetain d.last) =
      F.boundaryPosition (R.boundaryTurn leftRetain c.last) := by
    calc
      _ = G.boundaryPosition d.last + G.germDirection d.last.val := by
        rw [G.germDirection_boundary_positions]
        abel
      _ = F.boundaryPosition c.last + F.germDirection c.last.val := by
        exact congrArg₂ (· + ·) (positions (Fin.last n)) (vectors (Fin.last n))
      _ = _ := by rw [F.germDirection_boundary_positions]; abel
  apply congrArg (fun vertices : Fin (n + 2) → Plane =>
    (⟨vertices⟩ : PolygonalChain Plane (n + 1)))
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.lastCases_last, Fin.lastCases_last]
    exact congrArg Cap.horizontal endpoint
  · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    exact congrArg Cap.horizontal (positions k)


/-- Physical vector equality preserves every actual intrinsic bank length, on either face side. -/
theorem boundaryBankLengths_eq_of_physical_bank_geometry
    (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
    (vectors : ∀ i, (K.folding.restrictFaces V).germDirection (d.point i).val =
      (K.folding.restrictFaces U).germDirection (c.point i).val) (i : Fin (n + 1)) :
    (C.restrictFaces V).boundaryBankLength (d.point i) =
      (C.restrictFaces U).boundaryBankLength (c.point i) := by
  rw [(K.folding.restrictFaces V).boundaryBankLength_eq_germDirection_norm,
    (K.folding.restrictFaces U).boundaryBankLength_eq_germDirection_norm, vectors]

end Unfoldings.ConvexCap
