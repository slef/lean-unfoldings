module

public import Unfoldings.Cap.AcuteJordanPhysicalBank
public import Unfoldings.Cap.AcuteJordanBankBudget
public import Unfoldings.Cap.JordanContourBankInterval

/-! Transport the exact geometric Jordan-bank budget to an original bank's actual turns. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance acuteOriginalBudgetMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (apex : Plane)

local notation "P" => K.projectedBoundaryChain U chain
local notation "J" => PolygonalChain.twoLinkClosure (K.projectedBoundaryChain U chain) apex

open Classical in
/-- When the closure surrounds the chosen physical bank, its two-link bound
transfers with no extra path-curvature allowance. -/
theorem abs_sum_acute_original_bank_turn_error_le
    (h k : Plane →L[ℝ] ℝ)
    (first : ∀ i : Fin (n + 1), 0 < h ((P).edge i))
    (last : ∀ i : Fin (n + 1), 0 < k ((P).edge i))
    (initial : h apex < h ((P).vertex 0))
    (terminal : k ((P).vertex (Fin.last (n + 1))) ≤ k apex)
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    (outside : (C.mateGerm Set.univ (C.includeRestrictedGerm U chain.first.val)).1.1 ∉
      K.jordanFaces J)
    {budget : ℝ}
    (bound : let contains := inside.trans interior_subset
      |∑ j ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range (P).path)
          ((P).twoClosingCorners apex),
        K.jordanContourTurnError jordan contains avoids j| ≤ budget) :
    |∑ k : Fin n, K.cutBoundaryTurnError U (chain.point k.succ)| ≤ budget := by
  let trace := P
  let regionFaces := K.jordanFaces J
  let contains := inside.trans interior_subset
  have not_on_bank : apex ∉ Set.range trace.path := by
    intro member
    exact initial.not_ge
      (trace.path_linear_bounds h (fun i => (first i).le) member).1
  obtain ⟨d, matching, same⟩ := K.exists_acute_jordan_chain_on_original_bank U chain
    apex h k first last initial.le terminal jordan inside avoids outside
  have simple : Function.Injective trace.vertex := fun _ _ equal =>
    (trace.strictMono_linear_vertices h first).injective (congrArg h equal)
  have same_simple : Function.Injective (K.projectedBoundaryChain regionFaces d).vertex :=
    same.symm ▸ simple
  have actual := K.sum_jordan_chain_turnError_eq_geometric_bank jordan contains avoids d same_simple
  rw [same] at actual
  have corners := K.jordanGeometricBankIndices_congr_corners jordan contains avoids
    (Set.range trace.path) (trace.twoClosingCorners apex)
    {trace.vertex 0, trace.vertex (Fin.last (n + 1))}
    (by
      intro z bank
      have different : z ≠ apex := fun equal => not_on_bank (equal ▸ bank)
      simp [PolygonalChain.twoClosingCorners, different])
  have compare (i : Fin n) :
      K.cutBoundaryTurnError U (chain.point i.succ) =
        K.restrictedBoundaryTurnError regionFaces (d.point i.succ) := by
    rw [← K.cutBoundaryTurnError_univ]
    exact K.cutBoundaryTurnError_eq_of_original_banks U regionFaces chain d
      (fun j => (matching j).symm) i
  simp_rw [compare]
  rw [actual, ← corners]
  exact bound

end Unfoldings.ConvexCap
