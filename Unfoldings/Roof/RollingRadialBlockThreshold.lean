module

public import Unfoldings.Roof.MarkedCompletionRolling
public import Unfoldings.Geometry.RadialBlockThreshold
public import Unfoldings.Cap.Tilt

/-! One choice controls actual bank rolling and weighted radial loss at every smaller tilt. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance rollingRadialThresholdIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Positive local-heading and tilt tolerances precede the roof and every refinement.
They simultaneously control actual intrinsic bank rolling and weighted radial distortion. -/
theorem exists_uniform_rolling_radialBlock_threshold {ε L A δ : ℝ} (positive : 0 < ε)
    (length_constant : 0 ≤ L) (angular_constant : 0 ≤ A) (width : 0 < δ) :
    ∃ B > 0, ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ ψ ∈ Set.Ioc (0 : ℝ) φ, (3 : ℝ) / 4 ≤ Real.cos ψ ∧
        radialBlockError (Real.cos ψ)⁻¹ B L A δ < ε ∧
        ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
          K.TiltBound ψ → ∀ {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
            (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)),
            P.RadialFrom q 0 → 0 < dist q (P.vertex 0) →
            dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
            ∀ (height : Plane →ₗ[ℝ] ℝ),
              (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) → height (c - q) < 0 →
              0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
              ∀ E : K.CompletionMesh ψ (PlanarTopology.closedJordanDomain
                  (P.threeSegmentClosure q c)) (P.markedClosureEquations q c),
                E.cap.HasSmallRadialBankRolling P q c jordan B := by
  obtain ⟨B, Bpositive, θ, θbounds, distortion⟩ :=
    exists_positive_radialBlock_threshold positive length_constant angular_constant width
  obtain ⟨χ, χbounds, rolling⟩ :=
    ConvexCap.exists_uniform_tilt_radial_bank_budget.{0, 0} Bpositive
  let φ := min θ χ
  have φpositive : 0 < φ := lt_min θbounds.1 χbounds.1
  have φsmall : φ < Real.pi / 2 := (min_le_left _ _).trans_lt θbounds.2
  refine ⟨B, Bpositive, φ, ⟨φpositive, φsmall⟩, ?_⟩
  intro ψ ψbounds
  have ψθ : ψ ≤ θ := ψbounds.2.trans (min_le_left _ _)
  have ψχ : ψ ≤ χ := ψbounds.2.trans (min_le_right _ _)
  obtain ⟨normal, small_loss⟩ := distortion ψ ⟨ψbounds.1, ψθ⟩
  refine ⟨normal, small_loss, ?_⟩
  intro Face _ C K tilt n P q c jordan radial initial progress height supported outside outward E
  have ψsmall : ψ < Real.pi / 2 := ψbounds.2.trans_lt φsmall
  have actual_tilt := CompletionMesh.cap_tilt (E := E) ψbounds.1 ψsmall tilt
  have relaxed := ConvexCap.TiltBound.of_le E.cap actual_tilt ψbounds.1.le
    (by linarith [χbounds.2, Real.pi_pos]) ψχ
  obtain ⟨corner, total⟩ := rolling E.cap relaxed
  have contained := E.markedClosure_inside P q c jordan
  have avoids := E.markedClosure_avoids P q c
  obtain ⟨first, last, ends_eq, on_first, off_last, estimate⟩ :=
    E.cap.exists_radial_bank_rolling_comparison P q c jordan (contained.trans interior_subset)
      avoids contained radial initial progress height supported outside outward
      (E.markedClosure_corner_occurs P q c jordan 0)
      (E.markedClosure_corner_occurs P q c jordan 1)
      (show 0 ≤ B / (32 * Real.pi) by positivity) corner χbounds.1.le χbounds.2 relaxed
  exact ⟨contained, avoids, first, last, ends_eq, on_first, off_last, estimate.trans_lt total⟩

end Unfoldings.ConvexRoof
