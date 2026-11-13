module

public import Unfoldings.Geometry.Endpoints

public import Unfoldings.Roof.DevelopmentCoordinates
public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Geometry.AffineOrientation
public import Unfoldings.Complex.Connectivity

/-!
# One orientation relative to actual roof projection

The affine chart from each projected original triangle to its actual developed
copy has nonzero signed area scale. Strict opposite-side opening in both
placements forces these scales to have the same sign across retained seams.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexRoof C)

/-- The actual projected-to-developed charts agree on every retained original edge. -/
theorem roofPlacement_joined (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    D.roofPlacement K (C.left s).face (K.projectFace (C.left s).face x.val) =
      D.roofPlacement K (C.right s).face (K.projectFace (C.left s).face x.val) := by
  rw [D.roofPlacement_apply, K.projectedTriangle_joined s x, D.roofPlacement_apply]
  exact D.joined s kept x

/-- Area transport for the actual corner triple of any original face. -/
theorem roofPlacement_orient (f : Face) (a b c : Plane) :
    orient (D.place f a) (D.place f b) (D.place f c) =
      orientationScale (D.roofPlacement K f).toAffineMap *
        orient (K.projectFace f a) (K.projectFace f b) (K.projectFace f c) := by
  have area := orient_affineMap (D.roofPlacement K f).toAffineMap
    (K.projectFace f a) (K.projectFace f b) (K.projectFace f c)
  simpa only [AffineEquiv.coe_toAffineMap, D.roofPlacement_apply] using area

/-- Actual developed vectors transform signed planar area by the actual face-chart scale. -/
theorem roofDirection_orient (f : Face) (a b : Plane) :
    orient 0 (D.roofDirection K f a) (D.roofDirection K f b) =
      orientationScale (D.roofPlacement K f).toAffineMap * orient 0 a b := by
  change orient 0 ((D.roofPlacement K f).toAffineMap.linear a)
    ((D.roofPlacement K f).toAffineMap.linear b) = _
  exact orient_affine_linear _ a b

/-- The genuine original and developed triangles give a nonzero chart determinant. -/
theorem roofPlacement_scale_ne_zero (f : Face) :
    orientationScale (D.roofPlacement K f).toAffineMap ≠ 0 := by
  have actual := orient_map_ne_zero (D.place f) (C.triangle f).nondegenerate
  rw [D.roofPlacement_orient K f] at actual
  exact (mul_ne_zero_iff.mp actual).1

/-- Retained hinges force the same relative orientation on both actual incident faces. -/
theorem roofPlacement_scales_mul_pos (s : C.Seam) (kept : s ∈ retain) :
    0 < orientationScale (D.roofPlacement K (C.left s).face).toAffineMap *
      orientationScale (D.roofPlacement K (C.right s).face).toAffineMap := by
  let left := C.triangle (C.left s).face
  let right := C.triangle (C.right s).face
  let a := left.vertex (C.left s).edge
  let b := left.vertex (Triangle.next (C.left s).edge)
  let c := left.opposite (C.left s).edge
  let d := right.opposite (C.right s).edge
  let x : left.Edge (C.left s).edge := left.endpoint (C.left s).edge false
  let y : left.Edge (C.left s).edge := left.endpoint (C.left s).edge true
  have first := D.roofPlacement_joined K s kept x
  have last := D.roofPlacement_joined K s kept y
  change D.roofPlacement K (C.left s).face (K.projectFace (C.left s).face a) =
    D.roofPlacement K (C.right s).face (K.projectFace (C.left s).face a) at first
  change D.roofPlacement K (C.left s).face (K.projectFace (C.left s).face b) =
    D.roofPlacement K (C.right s).face (K.projectFace (C.left s).face b) at last
  have area := orient_affineMap (D.roofPlacement K (C.right s).face).toAffineMap
    (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
    (K.projectFace (C.right s).face d)
  change orient
    (D.roofPlacement K (C.right s).face (K.projectFace (C.left s).face a))
    (D.roofPlacement K (C.right s).face (K.projectFace (C.left s).face b))
    (D.roofPlacement K (C.right s).face (K.projectFace (C.right s).face d)) = _ at area
  rw [← first, ← last, D.roofPlacement_apply, D.roofPlacement_apply,
    D.roofPlacement_apply] at area
  have developed := D.opposite s kept
  change orient (D.place (C.left s).face a) (D.place (C.left s).face b)
    (D.place (C.left s).face c) *
      orient (D.place (C.left s).face a) (D.place (C.left s).face b)
        (D.place (C.right s).face d) < 0 at developed
  rw [D.roofPlacement_orient K (C.left s).face, area] at developed
  have original := K.projected_opposite s
  change orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
    (K.projectFace (C.left s).face c) *
      orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
        (K.projectFace (C.right s).face d) < 0 at original
  by_contra nonpositive
  have lower := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt nonpositive) original.le
  have negative : (orientationScale (D.roofPlacement K (C.left s).face).toAffineMap *
      orientationScale (D.roofPlacement K (C.right s).face).toAffineMap) *
    (orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
      (K.projectFace (C.left s).face c) *
    orient (K.projectFace (C.left s).face a) (K.projectFace (C.left s).face b)
      (K.projectFace (C.right s).face d)) < 0 := by nlinarith [developed]
  exact not_lt_of_ge lower negative

/-- All actual developed faces have the same relative orientation on a connected cut. -/
theorem roofPlacement_sign_constant (connected : C.DuallyConnected retain) (f g : Face) :
    (0 < orientationScale (D.roofPlacement K f).toAffineMap) ↔
      0 < orientationScale (D.roofPlacement K g).toAffineMap := by
  have related := connected f g
  induction related with
  | rel a b adjacent =>
    obtain ⟨s, kept, rfl, rfl⟩ := adjacent
    exact pos_iff_pos_of_mul_pos (D.roofPlacement_scales_mul_pos K s kept)
  | refl => rfl
  | symm _ _ _ previous => exact previous.symm
  | trans _ _ _ _ _ first last => exact first.trans last

/-- All face-chart scale products are positive on the actual connected retained mesh. -/
theorem roofPlacement_scales_mul_pos_of_connected (connected : C.DuallyConnected retain)
    (f g : Face) :
    0 < orientationScale (D.roofPlacement K f).toAffineMap *
      orientationScale (D.roofPlacement K g).toAffineMap := by
  have signs := D.roofPlacement_sign_constant K connected f g
  by_cases positive : 0 < orientationScale (D.roofPlacement K f).toAffineMap
  · exact mul_pos positive (signs.mp positive)
  · have first : orientationScale (D.roofPlacement K f).toAffineMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt positive) (D.roofPlacement_scale_ne_zero K f)
    have last : orientationScale (D.roofPlacement K g).toAffineMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => positive (signs.mpr h)))
        (D.roofPlacement_scale_ne_zero K g)
    exact mul_pos_of_neg_of_neg first last

end Unfoldings.FacewiseDevelopment
