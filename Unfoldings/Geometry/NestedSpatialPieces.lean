module

public import Unfoldings.Geometry.SpatialEnvelopePairings
public import Unfoldings.Geometry.ConstrainedTriangleCover
public import Unfoldings.Geometry.AffineEnd

/-! Exact rigid coordinates for nested physical triangulations of the same roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

/-- Fine cells contained in a whole original physical face. -/
def nestedPieceSet : Set U.Index :=
  {i | ∃ f : T.Index, (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier}

theorem nested_parent_unique (i : U.Index) {f g : T.Index}
    (first : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier)
    (last : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle g).carrier) : f = g := by
  by_contra different
  obtain ⟨p, member⟩ := (U.projectedTriangle i).interior_nonempty
  exact Set.disjoint_left.mp (T.separated different)
    (interior_mono first member) (interior_mono last member)

def nestedParent (i : T.nestedPieceSet U) : T.Index := i.property.choose

theorem nestedParent_contains (i : T.nestedPieceSet U) :
    (U.projectedTriangle i.val).carrier ⊆ (T.projectedTriangle (T.nestedParent U i)).carrier :=
  i.property.choose_spec

theorem nestedParent_eq (i : T.nestedPieceSet U) {f : T.Index}
    (contained : (U.projectedTriangle i.val).carrier ⊆ (T.projectedTriangle f).carrier) :
    T.nestedParent U i = f := T.nested_parent_unique U i.val (T.nestedParent_contains U i) contained

/-- The coordinate change uses the physical supporting planes, not planar projection lengths. -/
def nestedCoordinates (i : U.Index) (f : T.Index) : Plane ≃ᵃ[ℝ] Plane :=
  (family (U.support i)).project.trans (family (T.support f)).project.symm

theorem nestedCoordinates_inside (i : U.Index) (f : T.Index)
    (contained : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier)
    {x : Plane} (member : x ∈ (U.triangle i).carrier) :
    T.nestedCoordinates U i f x ∈ (T.triangle f).carrier := by
  rw [U.triangle_carrier] at member
  obtain ⟨p, member, rfl⟩ := member
  rw [T.triangle_carrier]
  exact ⟨p, contained member, by
    change (family (T.support f)).project.symm p =
      (family (T.support f)).project.symm
        ((family (U.support i)).project ((family (U.support i)).project.symm p))
    rw [(family (U.support i)).project.apply_symm_apply]⟩

/-- On contained faces the entire rigid affine maps agree in space. -/
theorem nestedCoordinates_spatial (i : U.Index) (f : T.Index)
    (contained : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier)
    (x : Plane) : T.placement f (T.nestedCoordinates U i f x) = U.placement i x := by
  have on_face {x : Plane} (member : x ∈ (U.triangle i).carrier) :
      T.placement f (T.nestedCoordinates U i f x) = U.placement i x := by
    rw [T.placement_eq_point f (T.nestedCoordinates_inside U i f contained member),
      U.placement_eq_point i member]
    change point family ((family (T.support f)).project
      ((family (T.support f)).project.symm ((family (U.support i)).project x))) = _
    rw [(family (T.support f)).project.apply_symm_apply]
  have maps : (T.placement f).toAffineMap.comp (T.nestedCoordinates U i f).toAffineMap =
      (U.placement i).toAffineMap := by
    apply (U.triangle i).affine_ext
    intro j
    exact on_face ((U.triangle i).vertex_mem j)
  exact congrArg (fun A : Plane →ᵃ[ℝ] Space => A x) maps

theorem nestedCoordinates_isometry (i : U.Index) (f : T.Index)
    (contained : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier) :
    Isometry (T.nestedCoordinates U i f) := by
  intro x y
  calc
    edist (T.nestedCoordinates U i f x) (T.nestedCoordinates U i f y) =
        edist (T.placement f (T.nestedCoordinates U i f x))
          (T.placement f (T.nestedCoordinates U i f y)) :=
      ((T.placement f).isometry.edist_eq _ _).symm
    _ = edist (U.placement i x) (U.placement i y) := by
      rw [T.nestedCoordinates_spatial U i f contained x,
        T.nestedCoordinates_spatial U i f contained y]
    _ = edist x y := (U.placement i).isometry.edist_eq x y

/-- A contained physical triangle has its exact original intrinsic Euclidean metric. -/
def nestedPlace (i : U.Index) (f : T.Index)
    (contained : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  let A := (T.nestedCoordinates_isometry U i f contained).affineIsometryOfStrictConvexSpace
  { AffineEquiv.ofBijective (φ := A.toAffineMap)
      ⟨A.injective, (T.nestedCoordinates U i f).surjective⟩ with norm_map := A.norm_map }

@[simp] theorem nestedPlace_apply (i : U.Index) (f : T.Index)
    (contained : (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier)
    (x : Plane) : T.nestedPlace U i f contained x = T.nestedCoordinates U i f x := rfl

end Unfoldings.SpatialEnvelope.Triangulation
