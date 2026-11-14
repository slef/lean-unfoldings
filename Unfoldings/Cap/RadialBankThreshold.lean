module

public import Unfoldings.Cap.RadialBankTurnComparison
public import Unfoldings.Cap.UniformCurvature
public import Unfoldings.Cap.Tilt

/-! A numerical small-tilt budget for actual radial bank errors, independent of the input mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Curvature, closing-section turns, and actual corner distortion share one uniform budget. -/
theorem exists_uniform_tilt_radial_bank_budget {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → K.RelativeCornerAngleError (η / (32 * Real.pi)) ∧
          C.totalInteriorAngularDefect Set.univ + 6 * φ +
            8 * Real.pi * (η / (32 * Real.pi)) < η := by
  obtain ⟨χ, χbounds, curvature⟩ := exists_uniform_tilt_totalCurvature_lt.{u, v}
    (show 0 < η / 4 by positivity)
  obtain ⟨θ, θbounds, corner⟩ := exists_uniform_tilt_relative_corner_angle_error.{u, v}
    (show 0 < η / (32 * Real.pi) by positivity)
  let φ := min χ (min θ (η / 24))
  have pp : 0 < φ := lt_min χbounds.1 (lt_min θbounds.1 (by positivity))
  have pχ : φ ≤ χ := min_le_left _ _
  have pθ : φ ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have pη : φ ≤ η / 24 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨φ, ⟨pp, pχ.trans_lt χbounds.2⟩, fun K tilt => ?_⟩
  have χtilt := TiltBound.of_le K tilt pp.le (by linarith [χbounds.2, Real.pi_pos]) pχ
  have θtilt := TiltBound.of_le K tilt pp.le (by linarith [θbounds.2, Real.pi_pos]) pθ
  refine ⟨corner K θtilt, ?_⟩
  have curve := curvature K χtilt
  have corners : 8 * Real.pi * (η / (32 * Real.pi)) = η / 4 := by
    field_simp
    ring
  rw [corners]
  linarith

open Classical in
/-- The actual three-link closure has arbitrarily small bank-turn error at one uniform tilt. -/
theorem exists_uniform_tilt_radial_bank_turn_error_lt {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
          (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
          (inside : P.threeSegmentClosure q c ⊆ interior K.footprint)
          (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier)
            (P.threeSegmentClosure q c)),
          0 < dist q (P.vertex 0) →
          dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
          ∀ (height : Plane →ₗ[ℝ] ℝ), 0 ≤ height (P.vertex 0 - q) →
            0 ≤ height (P.vertex (Fin.last n) - q) → height (c - q) < 0 →
            0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
            |∑ i ∈ K.jordanGeometricBankIndices jordan (inside.trans interior_subset) avoids
                (Set.range P.path) (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
              K.jordanContourTurnError jordan (inside.trans interior_subset) avoids i| < η := by
  obtain ⟨φ, bounds, budget⟩ := exists_uniform_tilt_radial_bank_budget.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P q c jordan inside avoids initial progress height first last outside
    outward
  obtain ⟨corner, total⟩ := budget K tilt
  exact (K.abs_radial_bank_turn_error_le P q c jordan (inside.trans interior_subset) avoids inside
    initial progress height first last outside outward (by positivity) corner bounds.1.le bounds.2
      tilt).trans_lt total

end Unfoldings.ConvexCap
