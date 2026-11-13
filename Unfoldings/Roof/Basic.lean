module

public import Unfoldings.Cap.Projection
public import Unfoldings.Boundary
public import Unfoldings.Complex.Folding
public import Unfoldings.Geometry.Angles
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Convex roofs over a convex domain with arbitrary boundary heights

The input consists of a spatial folding, actual supporting unit normals,
a convex projected footprint, injective vertical projection, and a convex projected
domain. Boundary heights are unrestricted. No cuts, monotone forest, development,
or nonoverlap certificate is input.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

structure ConvexRoof where
  folding : SpatialFolding C
  normal : Face → Space
  normal_unit : ∀ f, ‖normal f‖ = 1
  normal_upward : ∀ f, 0 < normal f 2
  normal_tangent : ∀ f x, inner ℝ (normal f) ((folding.place f).linear x) = 0
  supporting : ∀ f g (x : C.Cell g),
    inner ℝ (normal f) (folding.place g x.val - folding.place f 0) ≤ 0
  projection_injective : Function.Injective
    (fun x : C.Realization Set.univ => Cap.horizontal (folding.toSpace Set.univ x))
  convex_projection : Convex ℝ (Cap.horizontal '' folding.surface)
  interior_projection : (interior (Cap.horizontal '' folding.surface)).Nonempty

namespace ConvexRoof

variable {C} (K : ConvexRoof C)

def footprint : Set Plane := Cap.horizontal '' K.folding.surface

def TiltBound (φ : ℝ) : Prop := ∀ f, Real.cos φ ≤ K.normal f 2

def AcuteMargin (α : ℝ) : Prop := ∀ f (e : Fin 3),
  (C.triangle f).cornerAngle e ≤ Real.pi / 2 - α

include K in
theorem embedded : K.folding.IsEmbedded := by
  intro x y equal
  exact K.projection_injective (congrArg Cap.horizontal equal)

def toFootprint (x : C.Realization Set.univ) : K.footprint :=
  ⟨Cap.horizontal (K.folding.toSpace Set.univ x), K.folding.toSpace Set.univ x,
    (K.folding.range_toSpace Set.univ).subset ⟨x, rfl⟩, rfl⟩

theorem toFootprint_continuous : Continuous K.toFootprint :=
  (Cap.horizontalCLM.continuous.comp (K.folding.toSpace_lipschitz Set.univ).continuous).subtype_mk _

theorem toFootprint_surjective : Function.Surjective K.toFootprint := by
  rintro ⟨p, z, hz, equal⟩
  obtain ⟨x, image⟩ := (K.folding.range_toSpace Set.univ).symm.subset hz
  exact ⟨x, Subtype.ext ((congrArg Cap.horizontal image).trans equal)⟩

/-- The uncut intrinsic cap has exactly its actual projected subspace topology. -/
def footprintHomeomorph : C.Realization Set.univ ≃ₜ K.footprint :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective K.toFootprint
      ⟨fun _ _ equal => K.projection_injective (congrArg Subtype.val equal),
        K.toFootprint_surjective⟩) K.toFootprint_continuous

theorem face_projection_lower (f : Face) (x y : Plane) :
    K.normal f 2 * dist x y ≤
      dist (Cap.horizontal (K.folding.place f x)) (Cap.horizontal (K.folding.place f y)) := by
  have tangent : inner ℝ (K.normal f) (K.folding.place f x - K.folding.place f y) = 0 := by
    have linear := (K.folding.place f).toAffineMap.linear_apply_vsub x y
    change (K.folding.place f).linear (x - y) =
      K.folding.place f x - K.folding.place f y at linear
    rw [← linear]
    exact K.normal_tangent f (x - y)
  calc
    K.normal f 2 * dist x y = K.normal f 2 *
        dist (K.folding.place f x) (K.folding.place f y) :=
      congrArg (fun d : ℝ => K.normal f 2 * d) ((K.folding.place f).isometry.dist_eq x y).symm
    _ = K.normal f 2 * ‖K.folding.place f x - K.folding.place f y‖ := by rw [dist_eq_norm]
    _ ≤ ‖Cap.horizontal (K.folding.place f x - K.folding.place f y)‖ :=
      Cap.normal_tangent_projection_lower _ _ (K.normal_unit f) (K.normal_upward f).le tangent
    _ = dist (Cap.horizontal (K.folding.place f x)) (Cap.horizontal (K.folding.place f y)) := by
      rw [map_sub, dist_eq_norm]

end ConvexRoof
end Unfoldings
