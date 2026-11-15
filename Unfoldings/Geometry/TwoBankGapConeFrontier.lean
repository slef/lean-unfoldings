module

public import Unfoldings.Geometry.TwoBankGapCornerChart
public import Unfoldings.Geometry.ComplexBankGerm
public import Unfoldings.Geometry.LocalConeRegularClosed

/-! Actual gap corner cones retain precisely their original physical bank directions. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- Any exact local homogeneous gap model has the original physical bank directions as boundary. -/
theorem frontier_twoBankGap_cone (common : Q.start = R.start) (x : ℂ) (cone : Set ℂ)
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x,
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z - x ∈ cone) :
    frontier cone = R.complexCarrierGerm x ∪ Q.complexCarrierGerm x := by
  apply frontier_local_cone_eq x radial
    (fun v _r positive => by
      simp only [Set.mem_union, mem_complexCarrierGerm_smul_iff _ _ _ positive])
    near
  filter_upwards [R.eventually_mem_carrier_iff_complexGerm x,
    Q.eventually_mem_carrier_iff_complexGerm x] with z first last
  rw [R.frontier_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common]
  simp only [Set.mem_union, first, last]

/-- Away from the common source, the other actual bank contributes no corner direction. -/
theorem frontier_twoBankGap_cone_at_first_bank (common : Q.start = R.start) (x : ℂ)
    (on_bank : x ∈ R.carrier) (not_source : x ≠ R.start) (cone : Set ℂ)
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x,
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z - x ∈ cone) : frontier cone = R.complexCarrierGerm x := by
  have outside : x ∉ Q.carrier := by
    intro last
    have both : x ∈ R.carrier ∩ Q.carrier := ⟨on_bank, last⟩
    rw [R.twoBank_carriers_inter Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common] at both
    exact not_source (Set.mem_singleton_iff.mp both)
  rw [R.frontier_twoBankGap_cone Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common x cone radial near,
    (Q.complexCarrierGerm_eq_empty_iff x).mpr outside, Set.union_empty]

/-- The actual geometric gap agrees locally with the constructed active-inequality model. -/
theorem eventually_mem_twoBankGap_iff_regionGerm
    (S : Set (↥(R.equations ∪ Q.equations) → Bool)) (finite : S.Finite)
    (cover : R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
      ⋃ σ ∈ S, AffineArrangement.closedChamber (R.bankEquation Q) σ) (x : ℂ) :
    ∀ᶠ z in 𝓝 x,
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z - x ∈ AffineArrangement.regionGerm
          (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x := by
  let : Fintype ↥(R.equations ∪ Q.equations) :=
    (R.finite_equations.union Q.finite_equations).fintype
  let : Fintype S := finite.fintype
  have cover' :
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
      ⋃ σ : S, AffineArrangement.closedChamber (R.bankEquation Q) σ.val := by
    rw [cover]
    ext z
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
  have near := AffineArrangement.eventually_mem_region_iff_germ
    (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x
  simpa only [← cover', AffineArrangement.translatedRegionGerm, Set.mem_ofPred_eq] using near

/-- The actual constructed corner cones are regular closed, including at all internal banks. -/
theorem closure_interior_twoBankGap_regionGerm
    (S : Set (↥(R.equations ∪ Q.equations) → Bool)) (finite : S.Finite)
    (cover : R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
      ⋃ σ ∈ S, AffineArrangement.closedChamber (R.bankEquation Q) σ) (x : ℂ) :
    closure (interior (AffineArrangement.regionGerm
      (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x)) =
        AffineArrangement.regionGerm (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x := by
  apply closure_interior_local_cone_eq x
    (R.twoBankGap_regular_closed Q first_outward first_nonzero last_outward last_nonzero
      positive_phase) _
    (R.eventually_mem_twoBankGap_iff_regionGerm Q first_outward first_nonzero last_outward
      last_nonzero positive_phase S finite cover x)
  intro v r positive
  simp only [AffineArrangement.regionGerm, Set.mem_iUnion,
    AffineArrangement.mem_cellGerm_smul_iff _ _ _ _ positive]

/-- Apply the boundary identity to the actual active-inequality corner construction.
No proposed boundary rays, corner angle or local manifold certificate are supplied. -/
theorem frontier_twoBankGap_regionGerm (common : Q.start = R.start)
    (S : Set (↥(R.equations ∪ Q.equations) → Bool)) (finite : S.Finite)
    (cover : R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase =
      ⋃ σ ∈ S, AffineArrangement.closedChamber (R.bankEquation Q) σ) (x : ℂ) :
    frontier (AffineArrangement.regionGerm (fun _ : S => R.bankEquation Q) (fun σ => σ.val) x) =
      R.complexCarrierGerm x ∪ Q.complexCarrierGerm x := by
  apply R.frontier_twoBankGap_cone Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common x _ _
    (R.eventually_mem_twoBankGap_iff_regionGerm Q first_outward first_nonzero last_outward
      last_nonzero positive_phase S finite cover x)
  intro v r positive
  simp only [AffineArrangement.regionGerm, Set.mem_iUnion,
    AffineArrangement.mem_cellGerm_smul_iff _ _ _ _ positive]

end Unfoldings.PolygonalRay
