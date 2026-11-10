module

public import Unfoldings.Topology.DiskDegree
public import Schoenflies.JordanSchoenflies

/-!
# Openness of injective continuous maps in the plane

The Jordan–Schönflies theorem straightens the image of a disk boundary. The
circle obstruction then proves that the straightened map covers exactly the
open disk on its interior. This gives the planar case of invariance of domain.
The upstream planar-topology proofs and their compatibility changes are
recorded in `vendor/schoenflies/UPSTREAM.md`.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def complexIsometry : ℂ ≃ₗᵢ[ℝ] Plane :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

def circleHomeomorph : AddCircle (1 : ℝ) ≃ₜ Metric.sphere (0 : Plane) 1 :=
  (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).trans
    (complexSphereHomeomorph complexIsometry)

def circleParameter : C(ℝ, Metric.sphere (0 : Plane) 1) :=
  ⟨fun t => circleHomeomorph (t : AddCircle (1 : ℝ)),
    circleHomeomorph.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))⟩

theorem circleParameter_zero_one : circleParameter 0 = circleParameter 1 := by
  have equal : ((0 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_zero, AddCircle.coe_period]
  exact congrArg circleHomeomorph equal

theorem circleParameter_injective_Ico : Set.InjOn circleParameter (Set.Ico 0 1) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  intro s hs t ht equal
  have quotient : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
    circleHomeomorph.injective equal
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs) (by simpa only [zero_add] using ht)).mp quotient

theorem circleParameter_surjective_Icc (z : Metric.sphere (0 : Plane) 1) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, circleParameter t = z := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let t := AddCircle.equivIco (1 : ℝ) 0 (circleHomeomorph.symm z)
  refine ⟨t.val, ⟨t.property.1, ?_⟩, ?_⟩
  · simpa only [zero_add] using t.property.2.le
  · change circleHomeomorph (t.val : AddCircle (1 : ℝ)) = z
    rw [AddCircle.coe_equivIco, circleHomeomorph.apply_symm_apply]

theorem isJordanCurve_range_of_sphere_embedding
    (f : C(Metric.sphere (0 : Plane) 1, Plane)) (injective : Function.Injective f) :
    Schoenflies.IsJordanCurve (Set.range f) := by
  refine ⟨fun t => f (circleParameter t),
    ⟨(f.continuous.comp circleParameter.continuous).continuousOn,
      congrArg f circleParameter_zero_one, ?_⟩, ?_⟩
  · intro s hs t ht equal
    exact circleParameter_injective_Ico hs ht (injective equal)
  · ext y
    constructor
    · rintro ⟨t, _, equal⟩
      exact ⟨circleParameter t, equal⟩
    · rintro ⟨z, equal⟩
      obtain ⟨t, ht, point⟩ := circleParameter_surjective_Icc z
      exact ⟨t, ht, (congrArg f point).trans equal⟩

theorem isJordanCurve_unitSphere : Schoenflies.IsJordanCurve (Metric.sphere (0 : Plane) 1) := by
  have image : Set.range (Subtype.val : Metric.sphere (0 : Plane) 1 → Plane) =
      Metric.sphere (0 : Plane) 1 := Subtype.range_val
  rw [← image]
  exact isJordanCurve_range_of_sphere_embedding ⟨Subtype.val, continuous_subtype_val⟩
    Subtype.val_injective

theorem isOpen_range_diskInterior_of_injective
    (f : C(Metric.closedBall (0 : Plane) 1, Plane)) (injective : Function.Injective f) :
    IsOpen (Set.range (f.comp openBallDiskInclusion)) := by
  let boundary := f.comp (unitSphereDiskInclusion (E := Plane))
  have inclusion_injective : Function.Injective (unitSphereDiskInclusion (E := Plane)) := by
    intro a b equal
    exact Subtype.ext (congrArg (fun p : Metric.closedBall (0 : Plane) 1 => p.val) equal)
  have boundary_injective : Function.Injective boundary := injective.comp inclusion_injective
  let H : Metric.sphere (0 : Plane) 1 ≃ₜ Set.range boundary :=
    (boundary.continuous.isClosedEmbedding boundary_injective).isEmbedding.toHomeomorph
  obtain ⟨F, agrees⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (isJordanCurve_range_of_sphere_embedding boundary boundary_injective)
    isJordanCurve_unitSphere H.symm
  let g : C(Metric.closedBall (0 : Plane) 1, Plane) :=
    ⟨F ∘ f, F.continuous.comp f.continuous⟩
  have fixed (z : Metric.sphere (0 : Plane) 1) : g (unitSphereDiskInclusion z) = z.val := by
    have point := agrees (H z)
    change F (boundary z) = (H.symm (H z)).val at point
    change F (boundary z) = z.val
    simpa only [H.symm_apply_apply] using point
  have image_g := range_openBall_of_injective_fixes_sphere
    (not_contractible_unitSphere complexIsometry) g (F.injective.comp injective) fixed
  have image : Set.range (f.comp openBallDiskInclusion) =
      F ⁻¹' Metric.ball (0 : Plane) 1 := by
    conv_rhs => rw [← image_g]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, equal⟩
      exact ⟨x, F.injective equal⟩
  rw [image]
  exact Metric.isOpen_ball.preimage F.continuous

theorem isOpen_range_of_continuous_injective {U : Set Plane} (open_U : IsOpen U)
    (f : C(U, Plane)) (injective : Function.Injective f) : IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, rfl⟩
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp open_U x.val x.property
  have half_pos : 0 < ε / 2 := half_pos positive
  have inside (z : Metric.closedBall (0 : Plane) 1) : x.val + (ε / 2) • z.val ∈ U := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos half_pos]
    have bound : ‖z.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    exact (mul_le_of_le_one_right half_pos.le bound).trans_lt (by linarith)
  have continuous_coordinates : Continuous
      (fun z : Metric.closedBall (0 : Plane) 1 => x.val + (ε / 2) • z.val) := by fun_prop
  let coordinates : C(Metric.closedBall (0 : Plane) 1, U) :=
    ⟨fun z => ⟨x.val + (ε / 2) • z.val, inside z⟩,
      continuous_coordinates.subtype_mk inside⟩
  have coordinates_injective : Function.Injective coordinates := by
    intro a b equal
    apply Subtype.ext
    have point := congrArg Subtype.val equal
    change x.val + (ε / 2) • a.val = x.val + (ε / 2) • b.val at point
    exact (smul_right_injective Plane half_pos.ne') (add_left_cancel point)
  let patch := f.comp coordinates
  have open_patch := isOpen_range_diskInterior_of_injective patch
    (injective.comp coordinates_injective)
  have center : f x ∈ Set.range (patch.comp openBallDiskInclusion) := by
    refine ⟨⟨0, Metric.mem_ball_self zero_lt_one⟩, ?_⟩
    change f (coordinates ⟨0, Metric.mem_closedBall_self zero_le_one⟩) = f x
    apply congrArg f
    exact Subtype.ext (by simp [coordinates])
  apply Filter.mem_of_superset (open_patch.mem_nhds center)
  rintro _ ⟨z, rfl⟩
  exact ⟨coordinates (openBallDiskInclusion z), rfl⟩

theorem isOpenMap_of_continuous_injective {U : Set Plane} (open_U : IsOpen U)
    (f : C(U, Plane)) (injective : Function.Injective f) : IsOpenMap f := by
  intro S open_S
  let V : Set Plane := Subtype.val '' S
  have open_V : IsOpen V := open_U.isOpenEmbedding_subtypeVal.isOpenMap S open_S
  have inside (z : V) : z.val ∈ U := by
    obtain ⟨x, _, equal⟩ := z.property
    exact equal ▸ x.property
  let inclusion : C(V, U) :=
    ⟨fun z => ⟨z.val, inside z⟩, continuous_subtype_val.subtype_mk inside⟩
  have inclusion_injective : Function.Injective inclusion := by
    intro x y equal
    exact Subtype.ext (congrArg (fun p : U => p.val) equal)
  have open_range := isOpen_range_of_continuous_injective open_V (f.comp inclusion)
    (injective.comp inclusion_injective)
  have image : Set.range (f.comp inclusion) = f '' S := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, equal⟩ := z.property
      exact ⟨x, hx, congrArg f (Subtype.ext equal)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, ⟨x, hx, rfl⟩⟩, rfl⟩
  rwa [← image]

theorem isOpen_range_of_openEmbedding {A : Type*} [TopologicalSpace A]
    (i : A → Plane) (embedding : Topology.IsOpenEmbedding i)
    (f : C(A, Plane)) (injective : Function.Injective f) : IsOpen (Set.range f) := by
  let H := embedding.isEmbedding.toHomeomorph
  let g : C(Set.range i, Plane) := ⟨f ∘ H.symm, f.continuous.comp H.symm.continuous⟩
  have open_range := isOpen_range_of_continuous_injective embedding.isOpen_range g
    (injective.comp H.symm.injective)
  have image : Set.range g = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨H.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨H x, congrArg f (H.symm_apply_apply x)⟩
  rwa [← image]

end Unfoldings.PlanarTopology
