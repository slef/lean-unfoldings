module

public import Unfoldings.Cap.Topology
public import Unfoldings.Development
public import Unfoldings.Geometry.HingeConverse
public import Unfoldings.Complex.SubdivisionInteriors
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! A zero-tilt cap has its actual uncut planar embedding as a nonoverlapping development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexCap C) (flat : K.TiltBound 0)

include flat in
theorem normal_height_eq_one (f : Face) : K.normal f 2 = 1 := by
  have lower := flat f
  simp only [Real.cos_zero] at lower
  have identity := Cap.horizontal_norm_sq (K.normal f)
  rw [K.normal_unit] at identity
  nlinarith [sq_nonneg ‖Cap.horizontal (K.normal f)‖]

include flat in
theorem projected_face_isometry (f : Face) :
    Isometry (fun x : Plane => Cap.horizontal (K.folding.place f x)) := by
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · calc
      dist (Cap.horizontal (K.folding.place f x)) (Cap.horizontal (K.folding.place f y)) =
          ‖Cap.horizontal (K.folding.place f x - K.folding.place f y)‖ := by
        rw [map_sub, dist_eq_norm]
      _ ≤ ‖K.folding.place f x - K.folding.place f y‖ := Cap.horizontal_norm_le _
      _ = dist x y := by rw [← dist_eq_norm, (K.folding.place f).isometry.dist_eq]
  · simpa only [K.normal_height_eq_one flat f, one_mul] using K.face_projection_lower f x y

def flatPlace (f : Face) : Plane ≃ᵃⁱ[ℝ] Plane :=
  let A := (K.projected_face_isometry flat f).affineIsometryOfStrictConvexSpace
  { AffineEquiv.ofBijective (φ := A.toAffineMap)
      ⟨A.injective, affineIsometryEnd_surjective A⟩ with norm_map := A.norm_map }

@[simp] theorem flatPlace_apply (f : Face) (x : Plane) :
    K.flatPlace flat f x = Cap.horizontal (K.folding.place f x) := rfl

theorem flatPlace_joined (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    K.flatPlace flat (C.left s).face x.val =
      K.flatPlace flat (C.right s).face (C.identify s x).val :=
  congrArg Cap.horizontal (K.folding.joined s x)

theorem flatPlace_nonoverlapping {f g : Face} (different : f ≠ g) :
    Disjoint (interior (K.flatPlace flat f '' (C.triangle f).carrier))
      (interior (K.flatPlace flat g '' (C.triangle g).carrier)) := by
  rw [← rigid_image_interior, ← rigid_image_interior]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, first⟩ ⟨y, hy, last⟩
  let a : C.Cell f := ⟨x, interior_subset hx⟩
  let b : C.Cell g := ⟨y, interior_subset hy⟩
  have equal : C.faceMap Set.univ f a = C.faceMap Set.univ g b :=
    K.projection_injective (first.trans last.symm)
  have related := (C.faceMap_eq_iff Set.univ f g a b).mp equal
  have tags : (⟨f, a⟩ : C.Total) = ⟨g, b⟩ := C.eq_of_related_interior hx related
  exact different (congrArg Sigma.fst tags)

/-- A flat cap needs no cuts, even if its input mesh has arbitrary triangle angles. -/
def flatDevelopment : FacewiseDevelopment C Set.univ where
  place := K.flatPlace flat
  joined s _ := K.flatPlace_joined flat s
  opposite s _ := (C.triangle (C.left s).face).placed_opposite_of_disjoint
    (C.triangle (C.right s).face) (C.left s).edge (C.right s).edge (C.identify s)
    (K.flatPlace flat (C.left s).face) (K.flatPlace flat (C.right s).face)
    (K.flatPlace_joined flat s) (K.flatPlace_nonoverlapping flat (K.folding.incident_faces_ne s))

theorem flatDevelopment_nonoverlapping : (K.flatDevelopment flat).Nonoverlapping := by
  intro f g different
  exact K.flatPlace_nonoverlapping flat different

theorem flatDevelopment_toPlane (x : C.Realization Set.univ) :
    (K.flatDevelopment flat).toPlane x = Cap.horizontal (K.folding.toSpace Set.univ x) := by
  obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  rfl

theorem flatDevelopment_injective : Function.Injective (K.flatDevelopment flat).toPlane := by
  intro x y equal
  apply K.projection_injective
  simpa only [K.flatDevelopment_toPlane flat] using equal

end Unfoldings.ConvexCap
