module

public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Cap.ProjectedOpening
public import Unfoldings.Geometry.AffineOrientation
public import Unfoldings.Complex.Connectivity

/-!
# One orientation relative to actual cap projection

The affine chart from each projected original triangle to its actual developed
copy has nonzero signed area scale. Strict opposite-side opening in both
placements forces these scales to have the same sign across retained seams.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- The actual affine chart from horizontal coordinates to one rigidly developed face. -/
def projectedPlacement (f : Face) : Plane ≃ᵃ[ℝ] Plane :=
  (K.projectFaceEquiv f).symm.trans (D.place f).toAffineEquiv

@[simp] theorem projectedPlacement_apply (f : Face) (x : Plane) :
    D.projectedPlacement K f (K.projectFace f x) = D.place f x := by
  change D.place f ((K.projectFaceEquiv f).symm ((K.projectFaceEquiv f) x)) = D.place f x
  rw [AffineEquiv.symm_apply_apply]

@[simp] theorem projectedPlacement_linear (f : Face) (direction : Plane) :
    (D.projectedPlacement K f).linear direction = D.developedDirection K f direction := rfl

/-- The actual projected-to-developed charts agree on every retained original edge. -/
theorem projectedPlacement_joined (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    D.projectedPlacement K (C.left s).face (K.projectFace (C.left s).face x.val) =
      D.projectedPlacement K (C.right s).face (K.projectFace (C.left s).face x.val) := by
  rw [D.projectedPlacement_apply, K.projectedTriangle_joined s x, D.projectedPlacement_apply]
  exact D.joined s kept x

/-- Area transport for the actual corner triple of any original face. -/
theorem projectedPlacement_orient (f : Face) (a b c : Plane) :
    orient (D.place f a) (D.place f b) (D.place f c) =
      orientationScale (D.projectedPlacement K f).toAffineMap *
        orient (K.projectFace f a) (K.projectFace f b) (K.projectFace f c) := by
  have area := orient_affineMap (D.projectedPlacement K f).toAffineMap
    (K.projectFace f a) (K.projectFace f b) (K.projectFace f c)
  simpa only [AffineEquiv.coe_toAffineMap, D.projectedPlacement_apply] using area

/-- Actual developed vectors transform signed planar area by the actual face-chart scale. -/
theorem developedDirection_orient (f : Face) (a b : Plane) :
    orient 0 (D.developedDirection K f a) (D.developedDirection K f b) =
      orientationScale (D.projectedPlacement K f).toAffineMap * orient 0 a b := by
  change orient 0 ((D.projectedPlacement K f).toAffineMap.linear a)
    ((D.projectedPlacement K f).toAffineMap.linear b) = _
  exact orient_affine_linear _ a b

/-- The genuine original and developed triangles give a nonzero chart determinant. -/
theorem projectedPlacement_scale_ne_zero (f : Face) :
    orientationScale (D.projectedPlacement K f).toAffineMap ≠ 0 := by
  have actual := orient_map_ne_zero (D.place f) (C.triangle f).nondegenerate
  rw [D.projectedPlacement_orient K f] at actual
  exact (mul_ne_zero_iff.mp actual).1

/-- Retained hinges force the same relative orientation on both actual incident faces. -/
theorem projectedPlacement_scales_mul_pos (s : C.Seam) (kept : s ∈ retain) :
    0 < orientationScale (D.projectedPlacement K (C.left s).face).toAffineMap *
      orientationScale (D.projectedPlacement K (C.right s).face).toAffineMap := by
  let left := C.triangle (C.left s).face
  let right := C.triangle (C.right s).face
  let a := left.vertex (C.left s).edge
  let b := left.vertex (Triangle.next (C.left s).edge)
  let c := left.opposite (C.left s).edge
  let d := right.opposite (C.right s).edge
  let x : left.Edge (C.left s).edge := left.endpoint (C.left s).edge false
  let y : left.Edge (C.left s).edge := left.endpoint (C.left s).edge true
  have first := D.projectedPlacement_joined K s kept x
  have last := D.projectedPlacement_joined K s kept y
  change D.projectedPlacement K (C.left s).face (K.projectFace (C.left s).face a) =
    D.projectedPlacement K (C.right s).face (K.projectFace (C.left s).face a) at first
  change D.projectedPlacement K (C.left s).face (K.projectFace (C.left s).face b) =
    D.projectedPlacement K (C.right s).face (K.projectFace (C.left s).face b) at last
  have area := orient_affineMap (D.projectedPlacement K (C.right s).face).toAffineMap
    (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
    (K.projectFace (C.right s).face d)
  change orient
    (D.projectedPlacement K (C.right s).face (K.projectFace (C.left s).face a))
    (D.projectedPlacement K (C.right s).face (K.projectFace (C.left s).face b))
    (D.projectedPlacement K (C.right s).face (K.projectFace (C.right s).face d)) = _ at area
  rw [← first, ← last, D.projectedPlacement_apply, D.projectedPlacement_apply,
    D.projectedPlacement_apply] at area
  have developed := D.opposite s kept
  change orient (D.place (C.left s).face a) (D.place (C.left s).face b)
    (D.place (C.left s).face c) *
      orient (D.place (C.left s).face a) (D.place (C.left s).face b)
        (D.place (C.right s).face d) < 0 at developed
  rw [D.projectedPlacement_orient K (C.left s).face, area] at developed
  have original := K.projected_opposite s
  change orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
    (K.projectFace (C.left s).face c) *
      orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
        (K.projectFace (C.right s).face d) < 0 at original
  by_contra nonpositive
  have lower := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt nonpositive) original.le
  have negative : (orientationScale (D.projectedPlacement K (C.left s).face).toAffineMap *
      orientationScale (D.projectedPlacement K (C.right s).face).toAffineMap) *
    (orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
      (K.projectFace (C.left s).face c) *
    orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
      (K.projectFace (C.right s).face d)) < 0 := by nlinarith [developed]
  exact not_lt_of_ge lower negative

/-- All actual developed faces have the same relative orientation on a connected cut. -/
theorem projectedPlacement_sign_constant (connected : C.DuallyConnected retain) (f g : Face) :
    (0 < orientationScale (D.projectedPlacement K f).toAffineMap) ↔
      0 < orientationScale (D.projectedPlacement K g).toAffineMap := by
  have related := connected f g
  induction related with
  | rel a b adjacent =>
    obtain ⟨s, kept, rfl, rfl⟩ := adjacent
    exact pos_iff_pos_of_mul_pos (D.projectedPlacement_scales_mul_pos K s kept)
  | refl => rfl
  | symm _ _ _ previous => exact previous.symm
  | trans _ _ _ _ _ first last => exact first.trans last

/-- All face-chart scale products are positive on the actual connected retained mesh. -/
theorem projectedPlacement_scales_mul_pos_of_connected (connected : C.DuallyConnected retain)
    (f g : Face) :
    0 < orientationScale (D.projectedPlacement K f).toAffineMap *
      orientationScale (D.projectedPlacement K g).toAffineMap := by
  have signs := D.projectedPlacement_sign_constant K connected f g
  by_cases positive : 0 < orientationScale (D.projectedPlacement K f).toAffineMap
  · exact mul_pos positive (signs.mp positive)
  · have first : orientationScale (D.projectedPlacement K f).toAffineMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt positive) (D.projectedPlacement_scale_ne_zero K f)
    have last : orientationScale (D.projectedPlacement K g).toAffineMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => positive (signs.mpr h)))
        (D.projectedPlacement_scale_ne_zero K g)
    exact mul_pos_of_neg_of_neg first last

end Unfoldings.FacewiseDevelopment
