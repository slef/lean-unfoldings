module

public import Unfoldings.Cap.JordanChainTurnSum
public import Unfoldings.Cap.RadialBankTurnComparison
public import Unfoldings.Geometry.PolygonalVertexRays
public import Unfoldings.Geometry.RadialBankInterior
public import Unfoldings.Cap.JordanContourBankInterval

/-! Mesh-independent error bounds for the actual intrinsic radial bank chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

local instance jordanChainErrorMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable {n : ℕ}
  (d : ((C.restrictFaces (K.jordanFaces J)).boundarySystem Set.univ).Chain n)

local notation "P" => K.projectedBoundaryChain (K.jordanFaces J) d

include jordan contains avoids in
/-- The actual bank chain pays total curvature plus the three closing links and four
geometric corners. No index matching, fan-error sum equality or closing budget is supplied. -/
theorem abs_sum_jordan_chain_turnError_le_radial
    (source closing : Plane) (curve : (P).threeSegmentClosure source closing = J)
    (inside : J ⊆ interior K.footprint) (radial : (P).RadialFrom source 0)
    (initial : 0 < dist source ((P).vertex 0)) (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ k : Fin n, K.restrictedBoundaryTurnError (K.jordanFaces J) (d.point k.succ)| ≤
      C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  have genuine := K.projectedBoundaryChain_edge_ne_zero (K.jordanFaces J) d
  have ordered := (P).vertex_radius_strictMono_of_radial source radial genuine
  have injective : Function.Injective (P).vertex := fun _ _ same =>
    ordered.injective (congrArg (dist source) same)
  have progress : dist source ((P).vertex 0) <
      dist source ((P).vertex (Fin.last (n + 1))) :=
    ordered (by change 0 < n + 1; omega)
  have curve_jordan : Schoenflies.IsJordanCurve ((P).threeSegmentClosure source closing) := by
    rw [curve]
    exact jordan
  have curve_contains : (P).threeSegmentClosure source closing ⊆ K.footprint := by
    rw [curve]
    exact contains
  have curve_avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier)
      ((P).threeSegmentClosure source closing) := by
    rw [curve]
    exact avoids
  have curve_inside : (P).threeSegmentClosure source closing ⊆ interior K.footprint := by
    rw [curve]
    exact inside
  have estimate := K.abs_radial_bank_turn_error_le (P) source closing curve_jordan
    curve_contains curve_avoids curve_inside initial progress height
    (supported _ ((P).vertex_mem_path_range 0))
    (supported _ ((P).vertex_mem_path_range (Fin.last (n + 1)))) excluded outward
    error_nonnegative error nonnegative small tilt
  have transport (L : Set Plane) (same : (P).threeSegmentClosure source closing = L)
      (hj : Schoenflies.IsJordanCurve L) (hc : L ⊆ K.footprint)
      (ha : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) L) :
      |∑ j ∈ K.jordanGeometricBankIndices hj hc ha (Set.range (P).path)
          (radialClosingCorners source ((P).vertex 0) ((P).vertex (Fin.last (n + 1))) closing),
        K.jordanContourTurnError hj hc ha j| ≤
          C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
    subst L
    exact estimate
  have matched := transport J curve jordan contains avoids
  have corners := K.jordanGeometricBankIndices_congr_corners jordan contains avoids
    (Set.range (P).path)
    (radialClosingCorners source ((P).vertex 0) ((P).vertex (Fin.last (n + 1))) closing)
    {(P).vertex 0, (P).vertex (Fin.last (n + 1))}
    (fun _ member => (P).radialClosingCorners_on_bank source closing radial initial height
      supported excluded member)
  rw [corners, ← K.sum_jordan_chain_turnError_eq_geometric_bank jordan contains avoids d injective]
    at matched
  exact matched

end Unfoldings.ConvexCap
