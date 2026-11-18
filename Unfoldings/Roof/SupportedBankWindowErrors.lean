module

public import Unfoldings.Roof.SupportedBankWindows
public import Unfoldings.Roof.CompletionProjectedBankWindow

/-! Actual physical cap comparisons control the original bank chain's real metric phase error. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance supportedBankWindowErrorsMeshFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

open Classical in
/-- Eliminate auxiliary meshes and trims from the original chain's actual real phase bound. -/
theorem SupportedBankWindowComparisons.local_error
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (first n : ℕ) (fits : first + (n + 1) ≤ m)
    (short : let P := K.folding.projectedBoundaryChain (full.interval first (n + 1) fits)
      (∑ k : Fin n, InnerProductGeometry.angle
        (P.internalSourceRay control k.castSucc) (P.internalSourceRay control k.succ)) <
          Real.pi / 4) :
    |K.projectedMetricHeadingError (full.interval first (n + 1) fits)
      (Fin.last (n + 1))| < η := by
  obtain ⟨cut, s, t, start, finish, q, c, height, nearby, radial, initial,
      supported, excluded, outward, jordan, E, preserved, estimate⟩ :=
    comparisons first n fits short (δ := 1) zero_lt_one
  let actual := full.interval first (n + 1) fits
  let W := CompletionMesh.markedOriginalBankWindow actual cut s t q c
    start.2 finish.2 jordan E
  have matched : E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
      W.chain (Fin.last W.length) = K.projectedMetricHeading actual (Fin.last (n + 1)) :=
    W.terminal_projected_heading_eq finish.1
  have error : C.boundaryChainRollHeading actual (Fin.last (n + 1)) -
        E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
          W.chain (Fin.last W.length) =
      K.projectedMetricHeadingError actual (Fin.last (n + 1)) :=
    congrArg (fun h : ℝ => C.boundaryChainRollHeading actual (Fin.last (n + 1)) - h) matched
  exact Eq.mp (congrArg (fun e : ℝ => |e| < η) error) estimate

open Classical in
/-- Local comparisons bound differences of the full chain's unreduced real phase prefixes. -/
theorem SupportedBankWindowComparisons.phase_difference
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (first n : ℕ) (fits : first + (n + 1) ≤ m)
    (short : let P := K.folding.projectedBoundaryChain (full.interval first (n + 1) fits)
      (∑ k : Fin n, InnerProductGeometry.angle
        (P.internalSourceRay control k.castSucc) (P.internalSourceRay control k.succ)) <
          Real.pi / 4) :
    |K.projectedMetricHeadingError full ⟨first + n + 1, by omega⟩ -
      K.projectedMetricHeadingError full ⟨first, by omega⟩| < η := by
  have formula := K.projectedMetricHeadingError_interval full first (n + 1) fits
    (Fin.last (n + 1))
  have estimate := comparisons.local_error first n fits short
  have transported := Eq.mp (congrArg (fun e : ℝ => |e| < η) formula) estimate
  have index : (⟨first + (n + 1), by omega⟩ : Fin (m + 1)) =
      ⟨first + n + 1, by omega⟩ := Fin.ext (Nat.add_assoc first n 1).symm
  exact Eq.mp (congrArg (fun i : Fin (m + 1) =>
    |K.projectedMetricHeadingError full i -
      K.projectedMetricHeadingError full ⟨first, by omega⟩| < η) index) transported

end Unfoldings.ConvexRoof
