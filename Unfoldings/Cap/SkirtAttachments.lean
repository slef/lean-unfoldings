module

public import Unfoldings.Cap.SkirtRimComponents
public import Unfoldings.Geometry.RadialTailAttachment

/-! A skirt component attaches to an original rim vertex exactly at its seed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SkirtTailFamily

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} {q : Plane} (F : K.SkirtTailFamily Z q)

theorem rim_vertex_eq_seed (c : F.Component) (w : C.Vertex Set.univ)
    (boundary : C.IsBoundaryVertex Set.univ w)
    (member : K.projectedVertex w ∈ (F.componentTail c).carrier) :
    K.projectedVertex w = F.componentSeed c :=
  (F.componentTail c).inner_frontier_eq_seed_of_member K.convex_projection F.origin
    (F.outside _) ((K.projectedVertex_mem_frontier_iff w).mpr boundary) member

def AttachedComponent :=
  {c : F.Component // ∃ w : C.Vertex Set.univ,
    C.IsBoundaryVertex Set.univ w ∧ K.projectedVertex w = F.componentSeed c}

variable (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
  K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

/-- Original rim vertices and attached radial components are in bijection.
Independent components correspond to new skirt seeds and cannot merge original roots. -/
def boundaryComponentEquiv (lower : Z < 0) :
    {w : C.Vertex Set.univ // C.IsBoundaryVertex Set.univ w} ≃ F.AttachedComponent where
  toFun w := ⟨F.rimComponent covered w.val w.property, w.val, w.property,
    F.rim_vertex_eq_seed _ w.val w.property (F.rimComponent_mem covered w.val w.property)⟩
  invFun c := ⟨c.property.choose, c.property.choose_spec.1⟩
  left_inv w := by
    apply Subtype.ext
    apply K.projectedVertex_injective
    let c : F.AttachedComponent := ⟨F.rimComponent covered w.val w.property,
      w.val, w.property, F.rim_vertex_eq_seed _ w.val w.property
        (F.rimComponent_mem covered w.val w.property)⟩
    change K.projectedVertex c.property.choose = K.projectedVertex w.val
    exact c.property.choose_spec.2.trans
      (F.rim_vertex_eq_seed _ w.val w.property
        (F.rimComponent_mem covered w.val w.property)).symm
  right_inv c := by
    apply Subtype.ext
    apply F.rimComponent_eq_of_member lower covered c.property.choose
      c.property.choose_spec.1 c.val
    rw [c.property.choose_spec.2]
    exact (F.componentTail c.val).seed_mem

end Unfoldings.ConvexCap.SkirtTailFamily
