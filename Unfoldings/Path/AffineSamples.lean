module

public import Unfoldings.Path.Chart
public import Unfoldings.Geometry.RealAffine

/-!
# Continuing straight coordinates through a chart

The isometric coordinates of a geodesic on an entire parameter interval are
the restriction of one affine function of the original real time. Matching
any two distinct samples identifies that function on the whole interval.
The coordinate map may already include a rigid chart placement.
-/

@[expose] public section

noncomputable section

namespace Path

variable {X E : Type*} [PseudoEMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  {a b : X} {p : Path a b} {D : Set X}

theorem IsGeodesic.exists_affine_coordinates (geodesic : p.IsGeodesic)
    (f : D → E) (isometry : Isometry f) {r s : unitInterval} (ordered : r < s)
    (inside : ∀ t ∈ Set.Icc r s, p t ∈ D) :
    ∃ line : ℝ →ᵃ[ℝ] E, ∀ t (ht : t ∈ Set.Icc r s),
      f ⟨p t, inside t ht⟩ = line (t : ℝ) := by
  let first : D := ⟨p r, inside r ⟨le_rfl, ordered.le⟩⟩
  let last : D := ⟨p s, inside s ⟨ordered.le, le_rfl⟩⟩
  let parameter : ℝ →ᵃ[ℝ] ℝ :=
    ((s : ℝ) - (r : ℝ))⁻¹ • (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (r : ℝ))
  let line := (AffineMap.lineMap (f first) (f last)).comp parameter
  refine ⟨line, ?_⟩
  intro t ht
  let u := intervalFraction r s t ordered ht
  have point : intervalParam r s u = t := intervalParam_fraction r s t ordered ht
  have geodesic' := (geodesic.subpath r s).codRestrict D first.property last.property
    (fun v => inside _ (intervalParam_mem_Icc ordered.le v))
  have straight := geodesic'.map_eq_lineMap f isometry.lipschitzWith (isometry first last) u
  change f ⟨p (intervalParam r s u), _⟩ =
    AffineMap.lineMap (f first) (f last) (u : ℝ) at straight
  simp only [point] at straight
  change f ⟨p t, inside t ht⟩ = AffineMap.lineMap (f first) (f last)
    (((s : ℝ) - (r : ℝ))⁻¹ * ((t : ℝ) - (r : ℝ)))
  simpa only [u, intervalFraction, div_eq_inv_mul] using straight

theorem IsGeodesic.coordinates_eq_affine_of_two_samples (geodesic : p.IsGeodesic)
    (f : D → E) (isometry : Isometry f) {r s : unitInterval} (ordered : r < s)
    (inside : ∀ t ∈ Set.Icc r s, p t ∈ D) (line : ℝ →ᵃ[ℝ] E)
    {u v : unitInterval} (different : u ≠ v) (hu : u ∈ Set.Icc r s) (hv : v ∈ Set.Icc r s)
    (first : f ⟨p u, inside u hu⟩ = line (u : ℝ))
    (last : f ⟨p v, inside v hv⟩ = line (v : ℝ)) :
    ∀ t (ht : t ∈ Set.Icc r s), f ⟨p t, inside t ht⟩ = line (t : ℝ) := by
  obtain ⟨actual, agrees⟩ := geodesic.exists_affine_coordinates f isometry ordered inside
  have distinct : (u : ℝ) ≠ (v : ℝ) := fun equal => different (Subtype.ext equal)
  have equal := Unfoldings.real_affine_ext actual line distinct
    ((agrees u hu).symm.trans first) ((agrees v hv).symm.trans last)
  intro t ht
  rw [agrees t ht, equal]

end Path
