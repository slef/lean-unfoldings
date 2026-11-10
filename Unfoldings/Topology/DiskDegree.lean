module

public import Unfoldings.Topology.CircleObstruction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Isometry

/-!
# A disk map fixing its boundary covers its interior

If an interior point were omitted, radial normalization about that point would
extend a degree-one sphere map across the disk. Moving the normalization center
to zero gives a homotopy from the sphere identity to this extendible map.
Contractibility of the disk would then contract the sphere, a contradiction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitDirection (x : {x : E // x ≠ 0}) : Metric.sphere (0 : E) 1 :=
  ⟨‖x.val‖⁻¹ • x.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr x.property⟩

theorem continuous_unitDirection : Continuous (unitDirection (E := E)) :=
  ((continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
    continuous_subtype_val).subtype_mk _

theorem unitDirection_of_sphere (z : Metric.sphere (0 : E) 1) (h : z.val ≠ 0) :
    unitDirection ⟨z.val, h⟩ = z := by
  apply Subtype.ext
  have norm : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  change ‖z.val‖⁻¹ • z.val = z.val
  rw [norm, inv_one, one_smul]

def unitSphereDiskInclusion : C(Metric.sphere (0 : E) 1, Metric.closedBall (0 : E) 1) :=
  ⟨fun z => ⟨z.val, Metric.sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem openBall_subset_range_of_fixes_sphere
    (essential : ¬ ContractibleSpace (Metric.sphere (0 : E) 1))
    (f : C(Metric.closedBall (0 : E) 1, E))
    (fixed : ∀ z : Metric.sphere (0 : E) 1, f (unitSphereDiskInclusion z) = z.val) :
    Metric.ball (0 : E) 1 ⊆ Set.range f := by
  classical
  intro y hy
  by_contra omitted
  have y_norm : ‖y‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have nonzero (x : Metric.closedBall (0 : E) 1) : f x - y ≠ 0 := by
    intro equal
    exact omitted ⟨x, sub_eq_zero.mp equal⟩
  let subtract : C(Metric.closedBall (0 : E) 1, {z : E // z ≠ 0}) :=
    ⟨fun x => ⟨f x - y, nonzero x⟩, (f.continuous.sub continuous_const).subtype_mk nonzero⟩
  let retract : C(Metric.closedBall (0 : E) 1, Metric.sphere (0 : E) 1) :=
    ⟨unitDirection ∘ subtract, continuous_unitDirection.comp subtract.continuous⟩
  have boundary_nonzero (p : unitInterval × Metric.sphere (0 : E) 1) :
      p.2.val - (p.1 : ℝ) • y ≠ 0 := by
    intro equal
    have sphere_norm : ‖p.2.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
    have small : ‖(p.1 : ℝ) • y‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1]
      exact (mul_le_of_le_one_left (norm_nonneg y) p.1.property.2).trans_lt y_norm
    rw [← sub_eq_zero.mp equal, sphere_norm] at small
    exact (lt_irrefl (1 : ℝ)) small
  let motion : C(unitInterval × Metric.sphere (0 : E) 1, {z : E // z ≠ 0}) :=
    ⟨fun p => ⟨p.2.val - (p.1 : ℝ) • y, boundary_nonzero p⟩,
      ((continuous_subtype_val.comp continuous_snd).sub
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).subtype_mk
          boundary_nonzero⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (retract.comp unitSphereDiskInclusion) :=
    { toContinuousMap := ⟨unitDirection ∘ motion, continuous_unitDirection.comp motion.continuous⟩
      map_zero_left := by
        intro z
        have equal : (motion (0, z)).val = z.val := by simp [motion]
        apply Subtype.ext
        change ‖(motion (0, z)).val‖⁻¹ • (motion (0, z)).val = z.val
        rw [equal]
        exact congrArg Subtype.val (unitDirection_of_sphere z (equal ▸ (motion (0, z)).property))
      map_one_left := by
        intro z
        apply Subtype.ext
        change ‖(motion (1, z)).val‖⁻¹ • (motion (1, z)).val =
          ‖(subtract (unitSphereDiskInclusion z)).val‖⁻¹ •
            (subtract (unitSphereDiskInclusion z)).val
        simp only [motion, subtract, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul, fixed] }
  let := (convex_closedBall (0 : E) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have null : retract.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic (Metric.closedBall (0 : E) 1)).comp_right retract
  obtain ⟨c, constant⟩ := null.comp_left unitSphereDiskInclusion
  exact essential ((contractible_iff_id_nullhomotopic _).mpr
    ⟨c, (show (ContinuousMap.id _).Homotopic (retract.comp unitSphereDiskInclusion) from ⟨H⟩).trans
      constant⟩)

omit [NormedSpace ℝ E] in
theorem norm_image_eq_one_iff_of_fixes_sphere
    (f : C(Metric.closedBall (0 : E) 1, E)) (injective : Function.Injective f)
    (fixed : ∀ z : Metric.sphere (0 : E) 1, f (unitSphereDiskInclusion z) = z.val)
    (x : Metric.closedBall (0 : E) 1) : ‖f x‖ = 1 ↔ ‖x.val‖ = 1 := by
  constructor
  · intro norm
    let z : Metric.sphere (0 : E) 1 := ⟨f x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using norm⟩
    have equal : x = unitSphereDiskInclusion z := injective (fixed z).symm
    exact (congrArg (fun p : Metric.closedBall (0 : E) 1 => ‖p.val‖) equal).trans norm
  · intro norm
    let z : Metric.sphere (0 : E) 1 := ⟨x.val, by
      simpa only [Metric.mem_sphere, dist_zero_right] using norm⟩
    have equal : unitSphereDiskInclusion z = x := rfl
    rw [← equal, fixed]
    exact norm

def openBallDiskInclusion : C(Metric.ball (0 : E) 1, Metric.closedBall (0 : E) 1) :=
  ⟨fun z => ⟨z.val, Metric.ball_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [NormedSpace ℝ E] in
theorem openBallDiskInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding (openBallDiskInclusion (E := E)) :=
  Topology.IsOpenEmbedding.inclusion Metric.ball_subset_closedBall
    (Metric.isOpen_ball.preimage continuous_subtype_val)

theorem range_openBall_of_injective_fixes_sphere
    (essential : ¬ ContractibleSpace (Metric.sphere (0 : E) 1))
    (f : C(Metric.closedBall (0 : E) 1, E)) (injective : Function.Injective f)
    (fixed : ∀ z : Metric.sphere (0 : E) 1, f (unitSphereDiskInclusion z) = z.val) :
    Set.range (f.comp openBallDiskInclusion) = Metric.ball (0 : E) 1 := by
  have nonempty_ball : (Metric.ball (0 : E) 1).Nonempty :=
    ⟨0, Metric.mem_ball_self zero_lt_one⟩
  let := isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : E) 1).isPreconnected
  let normMap : C(Metric.ball (0 : E) 1, ℝ) :=
    ⟨fun x => ‖f (openBallDiskInclusion x)‖, (f.continuous.comp
      openBallDiskInclusion.continuous).norm⟩
  have connected : IsPreconnected (Set.range normMap) := isPreconnected_range normMap.continuous
  have avoids_one (x : Metric.ball (0 : E) 1) : normMap x ≠ 1 := by
    intro equal
    have norm := (norm_image_eq_one_iff_of_fixes_sphere f injective fixed
      (openBallDiskInclusion x)).mp equal
    have small : ‖x.val‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.property
    exact (ne_of_lt small) norm
  obtain ⟨origin, image⟩ := openBall_subset_range_of_fixes_sphere essential f fixed
    (Metric.mem_ball_self zero_lt_one)
  have origin_norm : ‖origin.val‖ < 1 := by
    have bound : ‖origin.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using origin.property
    apply lt_of_le_of_ne bound
    intro equal
    have norm := (norm_image_eq_one_iff_of_fixes_sphere f injective fixed origin).mpr equal
    rw [image, norm_zero] at norm
    exact zero_ne_one norm
  have zero_member : (0 : ℝ) ∈ Set.range normMap := by
    refine ⟨⟨origin.val, by simpa only [Metric.mem_ball, dist_zero_right] using origin_norm⟩, ?_⟩
    change ‖f origin‖ = 0
    rw [image, norm_zero]
  have small (x : Metric.ball (0 : E) 1) : normMap x < 1 := by
    by_contra bound
    have one_member := connected.ordConnected.out zero_member (Set.mem_range_self x)
      (show (1 : ℝ) ∈ Set.Icc 0 (normMap x) from ⟨zero_le_one, not_lt.mp bound⟩)
    obtain ⟨z, equal⟩ := one_member
    exact avoids_one z equal
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    change normMap x < 1
    exact small x
  · intro member
    obtain ⟨x, image⟩ := openBall_subset_range_of_fixes_sphere essential f fixed member
    have inside : x.val ∈ Metric.ball (0 : E) 1 := by
      have bound : ‖x.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      rw [Metric.mem_ball, dist_zero_right]
      apply lt_of_le_of_ne bound
      intro equal
      have norm := (norm_image_eq_one_iff_of_fixes_sphere f injective fixed x).mpr equal
      rw [image] at norm
      have lower : ‖y‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using member
      exact (ne_of_lt lower) norm
    exact ⟨⟨x.val, inside⟩, image⟩

def complexSphereHomeomorph (L : ℂ ≃ₗᵢ[ℝ] E) : Circle ≃ₜ Metric.sphere (0 : E) 1 :=
  L.toHomeomorph.subtype (by
    intro z
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔ L z ∈ Metric.sphere (0 : E) 1
    simp only [Metric.mem_sphere, dist_zero_right, L.norm_map])

theorem not_contractible_unitSphere (L : ℂ ≃ₗᵢ[ℝ] E) :
    ¬ ContractibleSpace (Metric.sphere (0 : E) 1) := by
  intro contractible
  let := contractible
  exact not_contractible_circle (complexSphereHomeomorph L).contractibleSpace

end Unfoldings
