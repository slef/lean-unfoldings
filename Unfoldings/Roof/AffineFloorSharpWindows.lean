module

public import Unfoldings.Roof.ForwardBankChart
public import Unfoldings.Roof.AcuteBankWindows

/-! All original bank windows share one sharp curvature and tilt budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open Real

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance sharpWindowIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local notation "K" => T.roof inside

section OneWindow

variable {retain : Set T.pairedComplex.Seam} {n : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain (n + 1))

local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding (K)) bank

/-- A common forward direction suffices for the sharp bank bound. The
positive chart orientation is chosen from the actual traversal of this bank. -/
theorem abs_projectedMetricHeadingError_le_sharp_of_direction (axis : Plane) (unit : ‖axis‖ = 1)
    (progress : ∀ i, 0 < inner ℝ axis ((P).edge i))
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin (n + 1),
      (K).projectedVertex (ConvexRoof.originalBankTurnVertex bank i) ∈ interior (K).footprint)
    {φ Ω : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (curvature : ∀ {A : Type u} {equations : A → Plane →ᵃ[ℝ] ℝ}
      (L : T.LineRefinement equations), L.mesh.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω) :
    |(K).projectedMetricHeadingError bank (Fin.last (n + 1))| ≤
      2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω := by
  obtain ⟨E, forward, positive⟩ := (K).exists_forwardBankChart bank axis unit progress
  apply T.abs_projectedMetricHeadingError_le_sharp_acute inside E bank forward positive cut _ nonnegative
    small tilt curvature
  intro i
  rw [ConvexRoof.projectedVertex_reorient, ConvexRoof.footprint_reorient]
  change E ((K).projectedVertex (ConvexRoof.originalBankTurnVertex bank i)) ∈
    interior (E.toHomeomorph '' (K).footprint)
  rw [← E.toHomeomorph.image_interior]
  exact Set.mem_image_of_mem E (internal i)

end OneWindow

variable {retain : Set T.pairedComplex.Seam} {m : ℕ}
  (bank : (T.pairedComplex.boundarySystem retain).Chain m)

local notation "P" => SpatialFolding.projectedBoundaryChain (ConvexRoof.folding (K)) bank

/-- The sharp heading discrepancy is uniform on every interval of an actual
original bank, including its initial and terminal subpaths. -/
theorem abs_projectedMetricHeadingError_sub_le_sharp_of_direction (axis : Plane) (unit : ‖axis‖ = 1)
    (progress : ∀ i, 0 < inner ℝ axis ((P).edge i))
    (cut : ∀ i, ¬ T.pairedComplex.IsBoundaryEdge Set.univ (T.pairedComplex.germEdge (bank.point i).val))
    (internal : ∀ i : Fin m,
      (K).projectedVertex (T.pairedComplex.vertexForgetCuts (Set.subset_univ retain)
        (T.pairedComplex.boundaryEndVertex retain (bank.point i.succ))) ∈ interior (K).footprint)
    {φ Ω : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (Ω_nonneg : 0 ≤ Ω)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (curvature : ∀ {A : Type u} {equations : A → Plane →ᵃ[ℝ] ℝ}
      (L : T.LineRefinement equations), L.mesh.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω)
    (i j : Fin (m + 1)) (ordered : i ≤ j) :
    |(K).projectedMetricHeadingError bank i - (K).projectedMetricHeadingError bank j| ≤
      2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω := by
  by_cases equal : i = j
  · rw [equal, sub_self, abs_zero]
    have sine := Real.sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos])
    have delta : 0 ≤ arcsin (tan (φ / 2) ^ 2) := Real.arcsin_nonneg.mpr (sq_nonneg _)
    positivity
  have before : i.val < j.val := (lt_of_le_of_ne ordered equal : i < j)
  let n := j.val - i.val - 1
  have fits : i.val + (n + 1) ≤ m := by
    have bound := j.isLt
    dsimp only [n]
    omega
  let sub := bank.interval i.val (n + 1) fits
  let A := (K).folding.projectedBoundaryChain sub
  have geometry : A = (P).interval i.val (n + 2) (by omega) :=
    (K).folding.projectedBoundaryChain_interval bank i.val (n + 1) fits
  have forward (l : Fin (n + 2)) : 0 < inner ℝ axis (A.edge l) := by
    rw [geometry, PolygonalChain.interval_edge]
    exact progress _
  have sub_internal (l : Fin (n + 1)) :
      (K).projectedVertex (ConvexRoof.originalBankTurnVertex sub l) ∈ interior (K).footprint := by
    let t : Fin m := ⟨i.val + l.val, by have := l.isLt; omega⟩
    have same : sub.point l.succ = bank.point t.succ := by
      change bank.point (bank.intervalIndex i.val (n + 1) fits l.succ) = bank.point t.succ
      apply congrArg bank.point
      apply Fin.ext
      change i.val + (l.val + 1) = i.val + l.val + 1
      omega
    unfold ConvexRoof.originalBankTurnVertex
    rw [same]
    exact internal t
  have estimate := T.abs_projectedMetricHeadingError_le_sharp_of_direction inside sub axis unit
    forward (fun l => cut (bank.intervalIndex i.val (n + 1) fits l)) sub_internal
    nonnegative small tilt curvature
  have phase := (K).projectedMetricHeadingError_interval bank i.val (n + 1) fits (Fin.last (n + 1))
  have last_eq : (⟨i.val + (Fin.last (n + 1)).val, by omega⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    change i.val + (n + 1) = j.val
    dsimp only [n]
    omega
  rw [last_eq] at phase
  exact (abs_sub_comm _ _).trans_le ((congrArg abs phase).symm.le.trans estimate)

end Unfoldings.SpatialEnvelope.FloorMesh
