module

public import Unfoldings.Roof.CompatibleFreshSourceMargin
public import Unfoldings.Cap.SourceBankGapGeometry
public import Unfoldings.Cap.UniformCurvature
public import Unfoldings.Complex.BoundaryChainAperture

/-! Actual fresh-source banks construct complete canonical Jordan gaps at one uniform tilt. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance compatibleFreshSourceGapGeometryIndexFintype : Fintype (T).Index :=
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

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

/-- No bank, margin, opening list, tail bound or curvature budget is supplied: a single
positive tilt constructs the complete local gap for every actual positive fresh source. -/
theorem exists_uniform_freshSource_gap_geometry {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
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
        (m : ℕ) (span : (Fcut).parents.distanceToRoot SourceAt[contour,j.castSucc] = m + 1)
        (_curved : 0 < (T).pairedComplex.interiorAngularDefect Set.univ
          SourceAt[contour,j.castSucc]),
        let bank := (RollAt[contour,starts,j,fresh,m,span]).terminalEdgeRay
        let opened := bank.openings (PolygonalChain.castOpenings span
          ((T).pairedComplex.contourRootwardOpenings (Fcut).selection contour j.succ
            SourceAt[contour,j.castSucc]))
        OrientedBankGap bank opened := by
  let γ := Real.cos (2 * annularHistoryAngle (a / b) β) / 4
  have gamma_positive : 0 < γ := div_pos (fine_annular_radial_margin_pos small) (by norm_num)
  have cosine := Real.cos_le_one (2 * annularHistoryAngle (a / b) β)
  have gamma_small : γ ≤ 1 := by dsimp [γ]; linarith
  obtain ⟨φ, phi_bounds, margin⟩ := K.exists_uniform_freshSourceBank_margin compact nonempty R
    no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  obtain ⟨χ, chi_bounds, lower, curvature⟩ := ConvexCap.exists_positive_tilt_curvature_budget
    (show 0 < γ ^ 2 / 3 by positivity)
  let θ := min φ χ
  refine ⟨θ, ⟨lt_min phi_bounds.1 chi_bounds.1,
    (min_le_left _ _).trans_lt phi_bounds.2⟩, ?_⟩
  intro ψ psi_bounds normal contour starts j fresh m span curved
  have psi_phi : ψ ≤ φ := psi_bounds.2.trans (min_le_left _ _)
  have psi_chi : ψ ≤ χ := psi_bounds.2.trans (min_le_right _ _)
  have normal_chi (i) : Real.cos χ ≤ (M.plane i).normal 2 :=
    (Real.cos_le_cos_of_nonneg_of_le_pi psi_bounds.1.le
      (by linarith [chi_bounds.2, Real.pi_pos]) psi_chi).trans (normal i)
  have total := (cap).totalCurvature_le_normal_budget lower
    ((T).toTriangulation.normalizedCap_tilt conforming inside normal_chi)
  have budget : 3 * (T).pairedComplex.totalInteriorAngularDefect Set.univ < γ ^ 2 := by
    linarith [total.trans_lt curvature]
  let gamma_nn : ℝ≥0 := ⟨γ, gamma_positive.le⟩
  exact (cap).sourceBank_orientedGap (Fcut).selection (Fcut).boundary_roots contour starts
    j fresh curved m span RollAt[contour,starts,j,fresh,m,span]
    ((T).pairedComplex.boundaryChainRoll_edge_ne_zero
      ChainAt[contour,starts,j,fresh,m,span] (Fin.last m))
    gamma_nn gamma_positive gamma_small budget
    (margin ψ ⟨psi_bounds.1, psi_phi⟩ normal contour starts j fresh m span)

end Unfoldings.ConvexRoof
