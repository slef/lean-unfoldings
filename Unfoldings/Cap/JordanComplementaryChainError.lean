module

public import Unfoldings.Cap.JordanChainErrorBound
public import Unfoldings.Cap.SharpCurvatureBudget
public import Unfoldings.Cap.ComplementaryBankTurns
public import Unfoldings.Complex.BoundaryChainVertices
public import Unfoldings.Cap.RadialBankThreshold

/-! Complementary original fan sums along actual Jordan bank chains pay only cap curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

local instance jordanComplementChainMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable {n : ℕ}
  (d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n)

include jordan contains avoids in
/-- Each actual one-sided Jordan bank error is minus its selected original angle excess. -/
theorem jordan_chain_turnError_eq_neg_regional (k : Fin n) :
    K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ) =
      -K.regionalAngleExcess (K.jordanFaces J)
        (C.includeRestrictedVertexUniv (K.jordanFaces J)
          ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ))) := by
  have angle := K.jordan_vertex_angle_excess jordan contains avoids
    ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ))
  dsimp only [restrictedBoundaryTurnError]
  linarith

include jordan contains avoids in
/-- Switching to the complementary original face fans at all actual internal chain vertices
costs at most total original curvature. Vertex distinctness and interior status are derived. -/
theorem abs_sum_jordan_chain_complement_difference_le_curvature
    (inside : J ⊆ interior K.footprint) :
    |(∑ k : Fin n, K.regionalAngleExcess (K.jordanFaces J)ᶜ
      (C.includeRestrictedVertexUniv (K.jordanFaces J)
        ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ)))) -
      (∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ))| ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  let V := K.jordanFaces J
  let R := C.restrictFaces V
  let vertex (k : Fin n) := C.includeRestrictedVertexUniv V
    (R.boundaryEndVertex Set.univ (d.point k.succ))
  have injective : Function.Injective vertex := by
    intro k l equal
    apply Fin.succ_injective
    apply R.boundaryChain_vertices_injective Set.univ d
    exact K.jordan_includeRestrictedVertex_injective jordan contains avoids equal
  have internal (k : Fin n) : ¬ C.IsBoundaryVertex Set.univ (vertex k) := by
    apply (K.projectedVertex_mem_interior_iff _).mp
    apply inside
    exact (K.jordan_isBoundaryVertex_iff jordan contains avoids _).mp
      (R.boundaryEndAsVertex Set.univ (d.point k.succ)).property
  have sum := K.abs_sum_complementary_bank_turn_error_le V (Finset.univ.image vertex) (by
    intro w member
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp member
    exact internal k)
  rw [Finset.sum_image (fun _ _ _ _ same => injective same),
    Finset.sum_image (fun _ _ _ _ same => injective same)] at sum
  dsimp only [V, R, vertex] at sum
  simpa only [← K.jordan_chain_turnError_eq_neg_regional jordan contains avoids d] using sum

local notation "P" => K.projectedBoundaryChain (K.jordanFaces J) d

include jordan contains avoids in
/-- Either original face side has a mesh-independent radial comparison bound. This controls
the complementary fan weights; identifying them with a prescribed cut bank is separate. -/
theorem abs_sum_complementary_jordan_chain_error_le_radial
    (source closing : Plane) (curve : (P).threeSegmentClosure source closing = J)
    (inside : J ⊆ interior K.footprint) (radial : (P).RadialFrom source 0)
    (initial : 0 < dist source ((P).vertex 0)) (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ k : Fin n, K.regionalAngleExcess (K.jordanFaces J)ᶜ
      (C.includeRestrictedVertexUniv (K.jordanFaces J)
        ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ)))| ≤
      2 * C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  have comparison := K.abs_sum_jordan_chain_complement_difference_le_curvature
    jordan contains avoids d inside
  have bound := K.abs_sum_jordan_chain_turnError_le_radial jordan contains avoids d
    source closing curve inside radial initial height supported excluded outward
    error_nonnegative error nonnegative small tilt
  have triangle := abs_add_le
    ((∑ k : Fin n, K.regionalAngleExcess (K.jordanFaces J)ᶜ
      (C.includeRestrictedVertexUniv (K.jordanFaces J)
        ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ)))) -
      (∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ)))
    (∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ))
  rw [sub_add_cancel] at triangle
  linarith

include jordan contains avoids in
/-- Transfer the sharp contour estimate to both actual ordered banks. The
complementary bank adds at most the sharp total curvature of the cap. -/
theorem abs_sum_jordan_chain_banks_le_sharp
    (source closing : Plane) (inside : J ⊆ interior K.footprint)
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (bank_bound :
      |∑ j ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range (P).path)
          (radialClosingCorners source ((P).vertex 0) ((P).vertex (Fin.last (n + 1))) closing),
        K.jordanContourTurnError jordan contains avoids j| ≤
        shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ) :
    |∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ)| ≤
        shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ ∧
      |∑ k : Fin n, K.regionalAngleExcess (K.jordanFaces J)ᶜ
        (C.includeRestrictedVertexUniv (K.jordanFaces J)
          ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ)))| ≤
        shallowDevelopmentHeading φ := by
  rw [K.sum_jordanGeometricBankIndices_eq_chain jordan contains avoids d source closing radial
    initial height supported excluded] at bank_bound
  refine ⟨bank_bound, ?_⟩
  let original : ℝ := ∑ k : Fin n,
    K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ)
  let complement : ℝ := ∑ k : Fin n, K.regionalAngleExcess (K.jordanFaces J)ᶜ
    (C.includeRestrictedVertexUniv (K.jordanFaces J)
      ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ (d.point k.succ)))
  have difference : |complement - original| ≤ C.totalInteriorAngularDefect Set.univ :=
    K.abs_sum_jordan_chain_complement_difference_le_curvature jordan contains avoids d inside
  have curvature := K.totalCurvature_le_shallowDevelopmentCurvature nonnegative small tilt
  have sum := abs_add_le (complement - original) original
  rw [sub_add_cancel] at sum
  change |original| ≤ _ at bank_bound
  change |complement| ≤ _
  linarith only [difference, curvature, sum, bank_bound]

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap

universe u v

/-- One positive tilt controls either original bank side, independent of mesh size,
path length and valence. The complementary bank pays one extra total-curvature term. -/
theorem exists_uniform_tilt_complementary_bank_budget {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → K.RelativeCornerAngleError (η / (64 * Real.pi)) ∧
          2 * C.totalInteriorAngularDefect Set.univ + 6 * φ +
            8 * Real.pi * (η / (64 * Real.pi)) < η := by
  obtain ⟨φ, bounds, budget⟩ := exists_uniform_tilt_radial_bank_budget.{u, v}
    (show 0 < η / 2 by positivity)
  refine ⟨φ, bounds, fun K tilt => ?_⟩
  obtain ⟨corner, total⟩ := budget K tilt
  have coefficient : (η / 2) / (32 * Real.pi) = η / (64 * Real.pi) := by
    field_simp
    ring
  rw [coefficient] at corner total
  refine ⟨corner, ?_⟩
  have remainder : 0 ≤ 6 * φ + 8 * Real.pi * (η / (64 * Real.pi)) := by
    have nonnegative := bounds.1.le
    positivity
  linarith

end Unfoldings.ConvexCap
