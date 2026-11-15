module

public import Unfoldings.Cap.PhysicalChainErrorComparison
public import Unfoldings.Cap.RadialJordanPhysicalChain
public import Unfoldings.Cap.JordanChainErrorBound

/-! Actual radial cut-bank fan errors are controlled without any initial-side hypothesis. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance unconditionalOriginalRadialMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n) (source closing : Plane)

local notation "P" => K.projectedBoundaryChain U c
local notation "J" => PolygonalChain.threeSegmentClosure
  (K.projectedBoundaryChain U c) source closing

/-- The original physical radial bank pays at most twice total curvature plus the closing
and corner terms. Actual selected-side alternatives and all fan identities are derived. -/
theorem abs_sum_original_radial_chain_turnError_le_unconditional
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ k : Fin n, K.cutBoundaryTurnError U (c.point k.succ)| ≤
      2 * C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  let V := K.jordanFaces J
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
  have estimate := K.abs_sum_jordan_chain_turnError_le_radial jordan
    (inside.trans interior_subset) avoids d source closing (by rw [projected]) inside
    (by rw [projected]; exact radial) (by rw [projected]; exact initial) height
    (by rw [projected]; exact supported) excluded (by rw [projected]; exact outward)
    error_nonnegative error nonnegative small tilt
  have bank_bound : |∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ)| ≤
      C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
    simpa only [K.cutBoundaryTurnError_univ] using estimate
  linarith

end Unfoldings.ConvexCap
