module

public import Unfoldings.Cone.ComplementarySectorRadial
public import Unfoldings.Geometry.SourceGapPhysicalCollapse
public import Mathlib.Analysis.Convex.Contractible

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

theorem exists_radialFiber_parameterization (x : B.carrier) :
    let arc := Set.Icc (0 : ℝ) (Real.pi / 2)
    ∃ f : arc → PolygonalPoint G.model.region,
      Continuous f ∧ {y | G.projectFirstBank y = x} = Set.range f ∧
        (x.val ≠ B.start → Function.Injective f) ∧
        (x.val = B.start → ∀ s t, f s = f t) := by
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
  refine ⟨h.symm ∘ fromAngle, h.symm.continuous.comp cont, fiber_eq, ?_, ?_⟩
  · intro distinct t u equal
    have positive : 0 < R := NNReal.coe_pos.mp (dist_pos.mpr distinct.symm)
    have same : (R : ℂ) * polarRay t.val = (R : ℂ) * polarRay u.val :=
      congrArg Subtype.val (h.symm.injective equal)
    have bound (z : parameter) : z.val ∈ Set.Icc 0 (2 * Real.pi) :=
      ⟨z.property.1, z.property.2.trans (by linarith [Real.pi_pos])⟩
    apply Subtype.ext
    rcases polar_eq_heading_cases R positive.ne' t.val u.val (bound t) (bound u) same with
      same | ⟨_, high⟩ | ⟨high, _⟩
    · exact same
    · have upper := u.property.2
      linarith [Real.pi_pos]
    · have upper := t.property.2
      linarith [Real.pi_pos]
  · intro source t u
    have zero : R = 0 := by
      change nndist B.start x.val = 0
      rw [source, nndist_self]
    apply congrArg h.symm
    apply Subtype.ext
    change (R : ℂ) * polarRay t.val = (R : ℂ) * polarRay u.val
    simp [zero]

/-- Every radial fiber is path connected from one bank to the other, including the
degenerate fiber at the common source. -/
theorem isPathConnected_projectFirstBank_fiber (x : B.carrier) :
    IsPathConnected {y | G.projectFirstBank y = x} := by
  obtain ⟨f, continuous, same, _, _⟩ := G.exists_radialFiber_parameterization x
  rw [same]
  let : PathConnectedSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) (Real.pi / 2)).isPathConnected ⟨0, le_rfl, by positivity⟩)
  exact isPathConnected_range continuous

/-- Away from the common source, a radial fiber is homeomorphic to a closed interval. -/
def radialFiberHomeomorph (x : B.carrier) (distinct : x.val ≠ B.start) :
    Set.Icc (0 : ℝ) (Real.pi / 2) ≃ₜ {y | G.projectFirstBank y = x} := by
  classical
  let spec (f : Set.Icc (0 : ℝ) (Real.pi / 2) → PolygonalPoint G.model.region) :=
    Continuous f ∧ {y | G.projectFirstBank y = x} = Set.range f ∧
      (x.val ≠ B.start → Function.Injective f) ∧
      (x.val = B.start → ∀ s t, f s = f t)
  let witness : ∃ f, spec f := G.exists_radialFiber_parameterization x
  let f := witness.choose
  obtain ⟨continuous, same, injective, _⟩ := witness.choose_spec
  let g (t : Set.Icc (0 : ℝ) (Real.pi / 2)) : {y | G.projectFirstBank y = x} :=
    ⟨f t, same.symm ▸ Set.mem_range_self t⟩
  have bijective : Function.Bijective g := by
    constructor
    · intro t u equal
      exact injective distinct (congrArg Subtype.val equal)
    · intro y
      obtain ⟨t, h⟩ := (show y.val ∈ Set.range f from same ▸ y.property)
      exact ⟨t, Subtype.ext h⟩
  let : CompactSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g bijective)
    (continuous.subtype_mk _)

/-- Every single-gap radial fiber is contractible, including the source fiber. -/
theorem contractibleSpace_projectFirstBank_fiber (x : B.carrier) :
    ContractibleSpace {y | G.projectFirstBank y = x} := by
  by_cases at_source : x.val = B.start
  · obtain ⟨f, _, same, _, constant⟩ := G.exists_radialFiber_parameterization x
    have nonempty : Nonempty {y | G.projectFirstBank y = x} := by
      let t : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by positivity⟩
      exact ⟨⟨f t, same.symm ▸ Set.mem_range_self t⟩⟩
    have singleton : Subsingleton {y | G.projectFirstBank y = x} := by
      constructor
      intro u v
      obtain ⟨s, es⟩ := (show u.val ∈ Set.range f from same ▸ u.property)
      obtain ⟨t, et⟩ := (show v.val ∈ Set.range f from same ▸ v.property)
      exact Subtype.ext (es.symm.trans ((constant at_source s t).trans et))
    exact inferInstance
  · let : ContractibleSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
      (convex_Icc _ _).contractibleSpace ⟨0, le_rfl, by positivity⟩
    exact (G.radialFiberHomeomorph x at_source).symm.contractibleSpace


/-- An injective physical bank transfer preserves the contractible nonempty gap fibers. -/
theorem contractibleSpace_collapseTo_fiber {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (Q : PolygonalRay F n) (injective : Function.Injective (B.mapCarrier Q))
    (x : PolygonalPoint G.model.region) :
    ContractibleSpace {y | (G.collapseTo Q y).val = (G.collapseTo Q x).val} := by
  have same : {y | (G.collapseTo Q y).val = (G.collapseTo Q x).val} =
      {y | G.projectFirstBank y = G.projectFirstBank x} := by
    ext y
    exact ⟨fun h => injective (Subtype.ext h), fun h =>
      congrArg (fun z => (B.mapCarrier Q z).val) h⟩
  rw [same]
  exact G.contractibleSpace_projectFirstBank_fiber (G.projectFirstBank x)

end Unfoldings.OrientedBankGap
