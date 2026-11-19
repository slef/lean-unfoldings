module

public import Unfoldings.Cone.ComplementarySectorRadial
public import Unfoldings.Geometry.SourceGapBankRetraction

/-! Each source-only gap radius gives a continuous arc across its two original banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (B : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_out : B.Outward) (first_ne : B.direction ≠ 0)
  (second_out : Q.Outward) (second_ne : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (B.twoBankRatio Q first_out first_ne second_out second_ne r).im)

theorem nndist_start_twoBankFrame (z : ℂ) :
    nndist B.start (B.twoBankFrame Q first_out first_ne second_out second_ne positive_phase z) =
      ‖z‖₊ := by
  have radius (w : ℂ) : nndist B.start (B.bankFrame first_out first_ne w) = ‖w‖₊ := by
    apply NNReal.eq
    change dist B.start (B.bankFrame first_out first_ne w) = ‖w‖
    rw [dist_eq_norm', B.bankFrame_apply, add_sub_cancel_left, norm_mul]
    by_cases zero : w = 0
    · simp [zero]
    · rw [B.radialCoefficient_unit first_out first_ne _ (nnnorm_pos.mpr zero), one_mul]
  rw [twoBankFrame, Homeomorph.trans_apply, radius]
  exact NNReal.eq (norm_variableSectorHomeomorph _ _ _ _ _ _)

end Unfoldings.PolygonalRay

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {B : PolygonalRay ℂ n} {θ : ℝ} (G : OrientedBankGap B (B.rotateSuffix 0 θ))

/-- Every radial fiber is path connected from one bank to the other, including the
degenerate fiber at the common source. -/
theorem isPathConnected_projectFirstBank_fiber (x : B.carrier) :
    IsPathConnected {y | G.projectFirstBank y = x} := by
  let R := nndist B.start x.val
  let S := planarSector (Real.pi / 2)
  let parameter := Set.Icc (0 : ℝ) (Real.pi / 2)
  have angle_pos : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have angle_small : Real.pi / 2 < Real.pi := half_lt_self Real.pi_pos
  have region : S = closedAngularSector (Real.pi / 2) :=
    planarSector_eq_closedAngularSector angle_pos angle_small
  let fromAngle (t : parameter) : S :=
    ⟨(R : ℂ) * polarRay t.val, region.symm ▸ ⟨R, t.val, t.property, rfl⟩⟩
  have cont : Continuous fromAngle := by
    apply Continuous.subtype_mk
    change Continuous (fun t : parameter => (R : ℂ) * Complex.exp ((t.val : ℂ) * Complex.I))
    exact continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const))
  let h := G.sectorHomeomorph
  have on_radius (z : S) :
      nndist B.start (h.symm z).val = ‖z.val‖₊ :=
    B.nndist_start_twoBankFrame _ G.first_outward G.first_nonzero G.second_outward
      G.second_nonzero G.phase z.val
  have norm_radius (r : ℝ≥0) (t : ℝ) : ‖(r : ℂ) * polarRay t‖₊ = r := by
    apply NNReal.eq
    change ‖(r : ℂ) * polarRay t‖ = (r : ℝ)
    rw [norm_mul, norm_polarRay, mul_one, Complex.norm_real]
    exact Real.norm_of_nonneg r.property
  have fiber_eq : {y | G.projectFirstBank y = x} = Set.range (h.symm ∘ fromAngle) := by
    ext y
    constructor
    · intro equal
      have radial : nndist B.start y.val = R := by
        have image := congrArg (B.radialHomeomorph G.first_outward G.first_nonzero) equal
        rwa [projectFirstBank, Homeomorph.apply_symm_apply] at image
      let z := h y
      have inside : z.val ∈ closedAngularSector (Real.pi / 2) := region ▸ z.property
      obtain ⟨s, t, bounds, coordinate⟩ := inside
      have yr : nndist B.start (h.symm z).val = R :=
        (congrArg (fun u : PolygonalPoint G.model.region => nndist B.start u.val)
          (h.symm_apply_apply y)).trans radial
      have same : s = R := by
        have normal : ‖z.val‖₊ = s :=
          (congrArg (fun z : ℂ => ‖z‖₊) coordinate).trans (norm_radius s t)
        exact normal.symm.trans ((on_radius z).symm.trans yr)
      refine ⟨⟨t, bounds⟩, ?_⟩
      have arg : fromAngle ⟨t, bounds⟩ = z := Subtype.ext
        (coordinate.trans (congrArg (fun s : ℝ≥0 => (s : ℂ) * polarRay t) same)).symm
      exact (congrArg h.symm arg).trans (h.symm_apply_apply y)
    · rintro ⟨t, rfl⟩
      apply (B.radialHomeomorph G.first_outward G.first_nonzero).injective
      change (B.radialHomeomorph G.first_outward G.first_nonzero)
        (G.projectFirstBank (h.symm (fromAngle t))) = R
      rw [projectFirstBank, Homeomorph.apply_symm_apply, on_radius]
      exact norm_radius R t.val
  rw [fiber_eq]
  let : PathConnectedSpace parameter := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) (Real.pi / 2)).isPathConnected ⟨0, le_rfl, angle_pos.le⟩)
  exact isPathConnected_range (h.symm.continuous.comp cont)

end Unfoldings.OrientedBankGap
