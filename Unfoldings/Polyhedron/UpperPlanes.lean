module

public import Unfoldings.Polyhedron.FaceHalfspaces
public import Unfoldings.Geometry.SupportedPlane
public import Unfoldings.Cap.Gnomonic

/-! Original supporting faces with upward normals have genuine affine graph coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.SupportingNormals

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (N : F.SupportingNormals)

abbrev UpperFace := {f : Face // 0 < N.normal f 2}

def projectFace (_N : F.SupportingNormals) (f : Face) : Plane →ᵃ[ℝ] Plane :=
  Cap.horizontal.toAffineMap.comp (F.place f).toAffineMap

theorem tangent_chord (f : Face) (x y : Plane) :
    inner ℝ (N.normal f) (F.place f x - F.place f y) = 0 := by
  have chord := (F.place f).toAffineMap.linear_apply_vsub x y
  change (F.place f).linear (x - y) = F.place f x - F.place f y at chord
  rw [← chord]
  exact N.tangent f (x - y)

theorem projectFace_injective (f : Face) (upward : 0 < N.normal f 2) :
    Function.Injective (N.projectFace f) := by
  intro x y same
  have zero : F.place f x - F.place f y = 0 := by
    by_contra different
    apply Cap.tangent_horizontal_ne_zero (N.normal f) _ (N.unit f) upward
      (N.tangent_chord f x y) different
    change Cap.horizontal (F.place f x) = Cap.horizontal (F.place f y) at same
    rw [map_sub, same, sub_self]
  exact (F.place f).injective (sub_eq_zero.mp zero)

def projectFaceEquiv (f : N.UpperFace) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.ofBijective (φ := N.projectFace f.val)
    ⟨N.projectFace_injective f.val f.property,
      (N.projectFace f.val).linear_surjective_iff.mp
        (LinearMap.surjective_of_injective
          ((N.projectFace f.val).linear_injective_iff.mpr
            (N.projectFace_injective f.val f.property)))⟩

def supportHeight (f : Face) : Plane →ᵃ[ℝ] ℝ :=
  (N.normal f 2)⁻¹ •
    (AffineMap.const ℝ Plane (inner ℝ (N.normal f) (F.place f 0)) -
      (innerSL ℝ (Cap.horizontal (N.normal f))).toLinearMap.toAffineMap)

@[simp] theorem supportHeight_apply (f : Face) (p : Plane) :
    N.supportHeight f p =
      (inner ℝ (N.normal f) (F.place f 0) - inner ℝ (Cap.horizontal (N.normal f)) p) /
        N.normal f 2 := by
  simp [supportHeight, div_eq_mul_inv, mul_comm]

theorem supportHeight_face (f : N.UpperFace) (x : Plane) :
    N.supportHeight f.val (N.projectFace f.val x) = F.place f.val x 2 := by
  rw [supportHeight_apply, div_eq_iff f.property.ne']
  have tangent := N.on_plane f.val x
  rw [inner_sub_right] at tangent
  have split := Cap.horizontal_inner (N.normal f.val) (F.place f.val x)
  change inner ℝ (N.normal f.val) (F.place f.val x) =
    inner ℝ (Cap.horizontal (N.normal f.val)) (N.projectFace f.val x) +
      N.normal f.val 2 * F.place f.val x 2 at split
  linarith

theorem supporting_iff (f : N.UpperFace) (z : Space) :
    inner ℝ (N.normal f.val) (z - F.place f.val 0) ≤ 0 ↔
      z 2 ≤ N.supportHeight f.val (Cap.horizontal z) := by
  rw [supportHeight_apply, le_div_iff₀ f.property, inner_sub_right]
  have split := Cap.horizontal_inner (N.normal f.val) z
  constructor <;> intro bound <;> linarith

theorem on_support_iff (f : N.UpperFace) (z : Space) :
    inner ℝ (N.normal f.val) (z - F.place f.val 0) = 0 ↔
      z 2 = N.supportHeight f.val (Cap.horizontal z) := by
  rw [supportHeight_apply, eq_div_iff f.property.ne', inner_sub_right]
  have split := Cap.horizontal_inner (N.normal f.val) z
  constructor <;> intro equal <;> linarith

def upperPlane (f : N.UpperFace) : SpatialPlane where
  height := N.supportHeight f.val
  place := F.place f.val
  project := N.projectFaceEquiv f
  horizontal_place _ := rfl
  height_place x := (N.supportHeight_face f x).symm
  normal := N.normal f.val
  normal_unit := N.unit f.val
  normal_upward := f.property
  normal_tangent := N.tangent f.val

open Classical in
def upperFaces : Finset Face := Finset.univ.filter (fun f => 0 < N.normal f 2)

@[simp] theorem mem_upperFaces (f : Face) : f ∈ N.upperFaces ↔ 0 < N.normal f 2 := by
  classical
  simp [upperFaces]

end Unfoldings.SpatialFolding.SupportingNormals

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- A bounded full-dimensional convex polyhedron has an original upward supporting face. -/
theorem exists_upper_face : ∃ f : Face, 0 < N.normal f 2 := by
  classical
  by_contra none
  have downward (f : Face) : N.normal f 2 ≤ 0 := le_of_not_gt (fun h => none ⟨f, h⟩)
  obtain ⟨c, member, maximal⟩ := F.compact_vertexHull.exists_isMaxOn
    (P.interior_nonempty.mono interior_subset) (EuclideanSpace.proj 2).continuous.continuousOn
  let z := Cap.horizontalAtHeight (Cap.horizontal c) (c 2 + 1)
  have shift : z - c = Cap.northLift 0 := by
    ext i
    fin_cases i <;> simp [z, Cap.horizontalAtHeight, Cap.horizontal_apply, Cap.northLift]
  have vertical (n : Space) : inner ℝ n (Cap.northLift 0) = n 2 := by
    rw [Cap.horizontal_inner, Cap.northLift_horizontal, Cap.northLift_height]
    simp
  have supported : z ∈ F.vertexHull := by
    rw [P.vertexHull_eq_face_halfspaces N]
    intro f
    have identity : z - F.place f 0 = (c - F.place f 0) + (z - c) := by abel
    rw [identity, inner_add_right, shift, vertical]
    exact add_nonpos (N.supporting f c member) (downward f)
  have impossible := maximal supported
  change c 2 + 1 ≤ c 2 at impossible
  linarith

include P in
theorem upperFaces_nonempty : N.upperFaces.Nonempty := by
  obtain ⟨f, positive⟩ := P.exists_upper_face N
  exact ⟨f, (N.mem_upperFaces f).mpr positive⟩

end Unfoldings.SpatialFolding.ConvexBoundary
