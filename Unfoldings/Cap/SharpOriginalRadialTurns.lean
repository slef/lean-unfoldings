module

public import Unfoldings.Cap.UnconditionalOriginalRadialChainErrorBound
public import Unfoldings.Cap.SharpCurvatureBudget

/-! The sharp contour estimate transfers to either original radial cut bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance sharpOriginalRadialMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n) (source closing : Plane)

local notation "P" => K.projectedBoundaryChain U c
local notation "J" => PolygonalChain.threeSegmentClosure (K.projectedBoundaryChain U c) source closing

/-- A sharp absolute turn estimate on the geometric Jordan bank controls
the actual original cut bank. The opposite side costs at most one additional curvature budget. -/
theorem abs_sum_original_radial_chain_turnError_le_sharp
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (bank_bound : let contains := inside.trans interior_subset
      |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range (P).path)
          (radialClosingCorners source ((P).vertex 0) ((P).vertex (Fin.last (n + 1))) closing),
        K.jordanContourTurnError jordan contains avoids i| ≤
        shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ) :
    |∑ k : Fin n, K.cutBoundaryTurnError U (c.point k.succ)| ≤ shallowDevelopmentHeading φ := by
  let V := K.jordanFaces J
  let contains := inside.trans interior_subset
  obtain ⟨d, positions, vectors, projected⟩ := K.exists_radial_jordan_physical_chain U c
    source closing radial initial height supported excluded outward jordan inside avoids
  have strict := (P).vertex_radius_strictMono_of_radial source radial
    (K.projectedBoundaryChain_edge_ne_zero U c)
  have simple : Function.Injective (P).vertex := fun _ _ same =>
    strict.injective (congrArg (dist source) same)
  have internal := K.original_chain_vertex_internal_of_path_subset U c
    (fun _ member => inside (Or.inl member))
  have comparison := K.abs_sum_cut_turnError_le_of_physical_chain_geometry U V c d
    positions vectors simple internal
  have same_sum := K.sum_jordanGeometricBankIndices_eq_chain jordan contains avoids d source
    closing (by rw [projected]; exact radial) (by rw [projected]; exact initial) height
    (by rw [projected]; exact supported) excluded
  rw [projected] at same_sum
  have estimate : |∑ k : Fin n, K.restrictedBoundaryTurnError V (d.point k.succ)| ≤
      shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ := by
    rw [← same_sum]
    exact bank_bound
  have bank : |∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ)| ≤
      shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ := by
    simpa only [K.cutBoundaryTurnError_univ] using estimate
  have curvature := K.totalCurvature_le_shallowDevelopmentCurvature nonnegative small tilt
  linarith only [comparison, bank, curvature]

end Unfoldings.ConvexCap
