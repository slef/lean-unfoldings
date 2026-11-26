module

public import Unfoldings.FewestNets.AcuteLatitudeAnnularSides
public import Unfoldings.FewestNets.RevisedLatitudePolarMetric
public import Unfoldings.FewestNets.SphericalSelectorBoundary
public import Unfoldings.Geometry.RegularPolygonBoundary
public import Unfoldings.Geometry.MinorArcCone
public import Unfoldings.Geometry.NorthFrame

/-! The revised selectors have their literal spherical polygon boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap Module InnerProductGeometry

open AcuteLatitudeGrid (polarFrame polarRadius)

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

/-- Each selector fits in the open hemisphere of its actual chart. -/
theorem exists_selectorSphere_hemisphere (key : Selector a) :
    ∃ q : Space, ‖q‖ = 1 ∧ ∀ x ∈ selectorSphere positive small key, 0 < inner ℝ q x := by
  let T := selectorFrame key
  refine ⟨T.symm (northLift 0), (T.symm.norm_map _).trans northLift_zero_unit, ?_⟩
  intro x hx
  change T x ∈ gnomonicNormal '' selectorSlopes positive small key at hx
  rw [← T.inner_map_map, T.apply_symm_apply, horizontal_inner (northLift 0),
    northLift_horizontal, northLift_height, inner_zero_left, one_mul, zero_add]
  obtain ⟨p, _, eq⟩ := hx
  rw [← eq]
  exact gnomonicNormal_upward p

/-- The endpoints are the two successive input vertices, in the original
common sphere. -/
def annularSideEndpoint (i : AnnularTriangle a) (j : Fin 3) (b : Bool) : Space :=
  (rings a).annularVertices i (if b then j + 1 else j)

set_option maxHeartbeats 1000000 in
/-- The support forms of an annular triangle are its actual chord-basis
coordinates. A zero coordinate selects exactly the opposite minor arc. -/
def annularSelectorBoundary (i : AnnularTriangle a) :
    SphericalSelectorBoundary (Fin 3) (selectorSphere positive small (.inr i)) := by
  let basis := LatitudeRings.chordBasis (rings_oriented positive small) (.inr (.inl i))
  let form (j : Fin 3) := basis.coord (j + 2)
  have vertex (j : Fin 3) : basis j = (rings a).annularVertices i j :=
    LatitudeRings.chordBasis_apply (rings_oriented positive small) (.inr (.inl i)) j
  have membership (x : Space) :
      x ∈ selectorSphere positive small (.inr i) ↔ ‖x‖ = 1 ∧ ∀ j, 0 ≤ form j x := by
    change x ∈ annularChartFrame a i ⁻¹' (gnomonicNormal '' annularSlopeSelector positive small i) ↔ _
    rw [annularSlopeSelector_eq_chord positive small i]
    change (‖x‖ = 1 ∧ ∀ j, 0 ≤ basis.coord j x) ↔ _
    apply and_congr_right
    intro _
    constructor
    · exact fun all j => all (j + 2)
    · intro all j
      have h := all (j + 1)
      change 0 ≤ basis.coord ((j + 1) + 2) x at h
      have eq : (j + 1) + 2 = j := by fin_cases j <;> decide
      rwa [eq] at h
  refine ⟨annularSideEndpoint i, form, fun j => ?_, membership, fun j => ?_⟩
  · intro zero
    have value := DFunLike.congr_fun zero (basis (j + 2))
    change basis.coord (j + 2) (basis (j + 2)) = 0 at value
    simp at value
  · have ua : ‖basis j‖ = 1 := by rw [vertex]; exact (rings a).annularVertices_unit i _
    have ub : ‖basis (j + 1)‖ = 1 := by rw [vertex]; exact (rings a).annularVertices_unit i _
    have ne : basis j + basis (j + 1) ≠ 0 := by
      intro sum
      have z := congrArg (basis.coord j) sum
      have diff : j ≠ j + 1 := by fin_cases j <;> decide
      rw [map_add, map_zero, basis.coord_apply, basis.coord_apply,
        Basis.repr_self, Basis.repr_self, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne diff, add_zero] at z
      exact one_ne_zero z
    change {x ∈ selectorSphere positive small (.inr i) | form j x = 0} =
      closedMinorArc ((rings a).annularVertices i j) ((rings a).annularVertices i (j + 1))
    rw [← vertex, ← vertex]
    ext x
    rw [mem_closedMinorArc_iff_nonnegative_combination ua ub ne]
    change (x ∈ selectorSphere positive small (.inr i) ∧ form j x = 0) ↔ _
    have mem : x ∈ selectorSphere positive small (.inr i) ↔
        ‖x‖ = 1 ∧ ∀ k, 0 ≤ basis.coord k x := by
      change x ∈ annularChartFrame a i ⁻¹' (gnomonicNormal '' annularSlopeSelector positive small i) ↔ _
      rw [annularSlopeSelector_eq_chord positive small i]
      rfl
    rw [mem]
    constructor
    · rintro ⟨⟨unit, nonneg⟩, zero⟩
      refine ⟨unit, basis.coord j x, basis.coord (j + 1) x, nonneg j, nonneg (j + 1), ?_⟩
      have sum : x = ∑ k, basis.coord k x • basis k := (basis.sum_repr x).symm
      change basis.coord (j + 2) x = 0 at zero
      rw [Fin.sum_univ_three] at sum
      fin_cases j
      · change basis.coord 2 x = 0 at zero
        rw [zero, zero_smul, add_zero] at sum
        exact sum
      · change basis.coord 0 x = 0 at zero
        rw [zero, zero_smul, zero_add] at sum
        exact sum
      · change basis.coord 1 x = 0 at zero
        rw [zero, zero_smul, add_zero] at sum
        exact sum.trans (add_comm _ _)
    · rintro ⟨unit, c, d, c_nonneg, d_nonneg, eq⟩
      refine ⟨⟨unit, fun k => ?_⟩, ?_⟩
      · rw [eq, map_add, map_smul, map_smul]
        fin_cases j <;> fin_cases k <;> simp [c_nonneg, d_nonneg]
      · change basis.coord (j + 2) x = 0
        rw [eq, map_add, map_smul, map_smul]
        fin_cases j <;> simp

/-- A polar side in the original frame has the unsplit ring endpoints. -/
def polarSideEndpoint (pole : Fin 2) (j : Fin (rowSize a 0)) (b : Bool) : Space :=
  (selectorFrame (a := a) (.inl pole)).symm (gnomonicNormal
    (polarSlopeVertex a (if b then j.val + 1 else j.val)))

set_option maxHeartbeats 1000000 in
/-- Both polar selectors have exactly their ring sides, with support planes
in the original sphere's coordinates. -/
def polarSelectorBoundary (pole : Fin 2) :
    SphericalSelectorBoundary (Fin (rowSize a 0)) (selectorSphere positive small (.inl pole)) := by
  let T := selectorFrame (a := a) (.inl pole)
  let K := regularSlopePolygon polarFrame (rowSize a 0) (tan (polarRadius a))
  have enough := polar_rows_ge_six positive small
  have sides : 3 ≤ rowSize a 0 := by omega
  let B := regularPolygonSideDirections polarFrame sides (tan_polarRadius_bounds positive small).1
  let : Nonempty (Fin (rowSize a 0)) := ⟨⟨0, by omega⟩⟩
  let form (j : Fin (rowSize a 0)) := (B.sphericalSideForm j).comp T.toLinearEquiv.toLinearMap
  refine ⟨polarSideEndpoint pole, form, fun j => ?_, fun x => ?_, fun j => ?_⟩
  · intro equal
    apply B.sphericalSideForm_ne_zero j
    ext x
    change B.sphericalSideForm j x = 0
    have h := DFunLike.congr_fun equal (T.symm x)
    change B.sphericalSideForm j (T (T.symm x)) = 0 at h
    simpa only [T.apply_symm_apply] using h
  · change T x ∈ gnomonicNormal '' K ↔ ‖x‖ = 1 ∧ ∀ j, 0 ≤ B.sphericalSideForm j (T x)
    constructor
    · rintro ⟨p, hp, equal⟩
      have unit := (T.norm_map x).symm.trans
        ((congrArg norm equal).symm.trans (gnomonicNormal_unit p))
      have bound := (B.mem_gnomonicPolygon_iff _ (fun p hp =>
        norm_le_of_mem_regularSlopePolygon polarFrame sides hp) (x := T x) (by rwa [T.norm_map])).mp
        ⟨p, hp, equal⟩
      exact ⟨unit, bound⟩
    · rintro ⟨unit, bound⟩
      exact (B.mem_gnomonicPolygon_iff _ (fun p hp =>
        norm_le_of_mem_regularSlopePolygon polarFrame sides hp) (x := T x)
        (by rwa [T.norm_map])).mpr bound
  · have arc :
        closedMinorArc (polarSideEndpoint pole j false) (polarSideEndpoint pole j true) =
          T.symm '' (gnomonicNormal '' segment ℝ (polarSlopeVertex a j.val)
            (polarSlopeVertex a (j.val + 1))) := by
      rw [gnomonicNormal_image_segment, SpatialRotation.image_closedMinorArc_linearIsometry]
      rfl
    rw [arc]
    ext x
    constructor
    · rintro ⟨inside, active⟩
      change T x ∈ gnomonicNormal '' K at inside
      obtain ⟨p, hp, equal⟩ := inside
      change B.sphericalSideForm j (T x) = 0 at active
      rw [← equal, B.sphericalSideForm_gnomonic,
        mul_eq_zero, inv_eq_zero, norm_eq_zero] at active
      have level : inner ℝ (B.normal j) p = B.offset j := by
        rcases active with zero | zero
        · exact (northLift_ne_zero p zero).elim
        · exact (sub_eq_zero.mp zero).symm
      have side := (regularSlopePolygon_activeSide_eq polarFrame sides
        (tan_polarRadius_bounds positive small).1 j).subset ⟨hp, level⟩
      exact ⟨T x, ⟨p, side, equal⟩, T.symm_apply_apply x⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      obtain ⟨inside, active⟩ := (regularSlopePolygon_activeSide_eq polarFrame sides
        (tan_polarRadius_bounds positive small).1 j).symm.subset hp
      change T (T.symm (gnomonicNormal p)) ∈ gnomonicNormal '' K ∧
        B.sphericalSideForm j (T (T.symm (gnomonicNormal p))) = 0
      rw [T.apply_symm_apply]
      refine ⟨⟨p, inside, rfl⟩, ?_⟩
      rw [B.sphericalSideForm_gnomonic]
      change ‖northLift p‖⁻¹ *
        (tan (polarRadius a) * cos (π / (rowSize a 0 : ℝ)) -
          inner ℝ (regularSideNormal polarFrame j) p) = 0
      rw [active, sub_self, mul_zero]

end Unfoldings.FewestNets.RevisedLatitudeGrid
