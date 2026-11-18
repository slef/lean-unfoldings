module

public import Unfoldings.Roof.CompatibleFreshSourceBank
public import Unfoldings.Roof.UniformSourceStartBankMargin

/-! A fixed positive radial margin controls every actual complete fresh-source bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleFreshSourceMarginIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

/-- One tilt controls all constructed fresh-source banks, including leaf returns and the
first source edge. Routing, interior placement and the actual bank chain are all derived. -/
theorem exists_uniform_freshSourceBank_margin {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ (contour : (T).pairedComplex.BoundaryContour
          ((T).pairedComplex.selectedRetain (Fcut).selection))
        (starts : (T).pairedComplex.contourOriginalVertex (Fcut).selection contour 0 ∈
          (Fcut).parents.roots) (j : Fin contour.length)
        (fresh : SourceAt[contour,j.castSucc] ∉
          ((T).pairedComplex.contourFrontier (Fcut).selection contour j.castSucc).processed)
        (m : ℕ) (span : (Fcut).parents.distanceToRoot SourceAt[contour,j.castSucc] = m + 1),
        ∀ (k : Fin (m + 2)) (l : Fin (m + 1)), k.val ≤ l.val →
          (Real.cos (2 * annularHistoryAngle (a / b) β) / 4) *
            (‖((T).pairedComplex.boundaryChainRoll
                  ChainAt[contour,starts,j,fresh,m,span]).vertex l.castSucc -
                ((T).pairedComplex.boundaryChainRoll
                  ChainAt[contour,starts,j,fresh,m,span]).vertex k‖ *
              ‖((T).pairedComplex.boundaryChainRoll
                ChainAt[contour,starts,j,fresh,m,span]).edge l‖) ≤
            inner ℝ (((T).pairedComplex.boundaryChainRoll
                ChainAt[contour,starts,j,fresh,m,span]).vertex l.castSucc -
              ((T).pairedComplex.boundaryChainRoll
                ChainAt[contour,starts,j,fresh,m,span]).vertex k)
              (((T).pairedComplex.boundaryChainRoll
                ChainAt[contour,starts,j,fresh,m,span]).edge l) := by
  obtain ⟨θ, theta_bounds, radial⟩ := R.exists_uniform_sourceStart_bank_margin
    positive beta acute bpos ratio inner_disk upper small
  refine ⟨θ, theta_bounds, ?_⟩
  intro ψ psi_bounds normal contour starts j fresh m span
  exact radial ψ psi_bounds M.plane (T).toTriangulation conforming inside normal
    RetainAt[contour,j.succ] ChainAt[contour,starts,j,fresh,m,span]
    (K.compatibleMeshFreshSourceBankChain_follows compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts j fresh m span)
    (K.compatibleMeshFreshSourceBankChain_starts_interior compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts j fresh m span)

end Unfoldings.ConvexRoof
