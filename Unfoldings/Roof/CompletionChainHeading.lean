module

public import Unfoldings.Roof.CompletionChainFanRefinement
public import Unfoldings.Topology.FinitePrefixSum

/-! Whole physical bank refinements preserve real terminal headings exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainHeadingIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Counting each starting fan once, all inserted fan turns vanish. -/
theorem sum_starting_turns_eq :
    (∑ j : Fin (R.length + 1), (Real.pi - E.originalComplex.totalAngle
      (E.originalRetain retain) (E.originalComplex.boundaryEndVertex
        (E.originalRetain retain) (R.chain.point j)))) =
      ∑ i : Fin (n + 1), (Real.pi -
        C.totalAngle retain (C.boundaryEndVertex retain (coarse.point i))) := by
  let weight (j : Fin (R.length + 1)) := Real.pi - E.originalComplex.totalAngle
    (E.originalRetain retain) (E.originalComplex.boundaryEndVertex
      (E.originalRetain retain) (R.chain.point j))
  calc
    _ = ∑ j ∈ Finset.univ.image R.coarseIndex, weight j := by
      symm
      apply Finset.sum_subset (fun _ _ => Finset.mem_univ _)
      intro j _ outside
      have new : ∀ i, R.coarseIndex i ≠ j := by
        intro i equal
        exact outside (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, equal⟩)
      exact sub_eq_zero.mpr (R.totalAngle_eq_pi_of_new j new).symm
    _ = ∑ i : Fin (n + 1), weight (R.coarseIndex i) :=
      Finset.sum_image (fun _ _ _ _ equal => R.coarseIndex_injective equal)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [weight]
      rw [R.coarseIndex_totalAngle]

open Classical in
/-- The entire actual fine bank chain has exactly the old unreduced terminal heading.
This is an equality in the reals, with no reduction modulo a full rotation. -/
theorem terminal_heading_eq :
    E.originalComplex.boundaryChainRollHeading R.chain (Fin.last R.length) =
      C.boundaryChainRollHeading coarse (Fin.last n) := by
  have all := R.sum_starting_turns_eq
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at all
  have first := R.coarseIndex_totalAngle 0
  rw [R.coarseIndex_zero] at first
  rw [first] at all
  have fine_heading : E.originalComplex.boundaryChainRollHeading R.chain
      (Fin.last R.length) = ∑ k : Fin R.length, (Real.pi - E.originalComplex.totalAngle
        (E.originalRetain retain) (E.originalComplex.boundaryEndVertex
          (E.originalRetain retain) (R.chain.point k.succ))) :=
    fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)
  have old_heading : C.boundaryChainRollHeading coarse (Fin.last n) =
      ∑ k : Fin n, (Real.pi -
        C.totalAngle retain (C.boundaryEndVertex retain (coarse.point k.succ))) :=
    fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)
  rw [fine_heading, old_heading]
  linarith

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
