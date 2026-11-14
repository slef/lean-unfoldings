module

public import Unfoldings.Complex.AffineProjection
public import Unfoldings.Complex.Vertices

/-! Compatible affine projection preserves all actual seam chains and corner classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)

def affineProjectionInverseTotal (a : (C.affineProjectionComplex A joined).Total) : C.Total :=
  ⟨a.1, ⟨(A a.1).symm a.2.val, by
    obtain ⟨x, hx, same⟩ := ((C.triangle a.1).affineImage_carrier
      (A a.1).toAffineMap (A a.1).injective).subset a.2.property
    have coordinates : (A a.1).symm a.2.val = x := by
      rw [← same]
      exact (A a.1).symm_apply_apply x
    exact coordinates.symm ▸ hx⟩⟩

@[simp] theorem affineProjectionInverseTotal_apply (a : C.Total) :
    C.affineProjectionInverseTotal A joined (C.affineProjectionTotal A joined a) = a := by
  rcases a with ⟨f, x⟩
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact (A f).symm_apply_apply x.val

/-- Reverse projected seam crossings by the actual inverse face coordinates. -/
theorem affineProjection_inverse_glue (retain : Set C.Seam)
    {a b : (C.affineProjectionComplex A joined).Total}
    (related : (C.affineProjectionComplex A joined).glue retain a b) :
    C.glue retain (C.affineProjectionInverseTotal A joined a)
      (C.affineProjectionInverseTotal A joined b) := by
  obtain ⟨s, kept, x, rfl, rfl⟩ := related
  obtain ⟨y, hy, image⟩ := ((C.triangle (C.left s).face).affineImage_edge
    (A (C.left s).face).toAffineMap (A (C.left s).face).injective
    (C.left s).edge).subset x.property
  let original : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨y, hy⟩
  refine ⟨s, kept, original, ?_, ?_⟩
  · dsimp only [affineProjectionInverseTotal]
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    change (A (C.left s).face).symm x.val = y
    rw [← image]
    exact (A (C.left s).face).symm_apply_apply y
  · dsimp only [affineProjectionInverseTotal]
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    change (A (C.right s).face).symm x.val = (C.identify s original).val
    have coordinates : A (C.right s).face (C.identify s original).val = x.val :=
      (joined s original).symm.trans image
    rw [← coordinates]
    exact (A (C.right s).face).symm_apply_apply _

theorem affineProjection_eqvGen (retain : Set C.Seam) {a b : C.Total}
    (related : Relation.EqvGen (C.glue retain) a b) :
    Relation.EqvGen ((C.affineProjectionComplex A joined).glue retain)
      (C.affineProjectionTotal A joined a) (C.affineProjectionTotal A joined b) := by
  induction related with
  | rel a b h => exact Relation.EqvGen.rel _ _ (C.affineProjection_glue A joined retain h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ first last => exact Relation.EqvGen.trans _ _ _ first last

theorem affineProjection_inverse_eqvGen (retain : Set C.Seam)
    {a b : (C.affineProjectionComplex A joined).Total}
    (related : Relation.EqvGen ((C.affineProjectionComplex A joined).glue retain) a b) :
    Relation.EqvGen (C.glue retain) (C.affineProjectionInverseTotal A joined a)
      (C.affineProjectionInverseTotal A joined b) := by
  induction related with
  | rel a b h => exact Relation.EqvGen.rel _ _ (C.affineProjection_inverse_glue A joined retain h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ first last => exact Relation.EqvGen.trans _ _ _ first last

/-- The same tagged corners belong to exactly the same actual retained vertex classes. -/
theorem affineProjection_corner_related_iff (retain : Set C.Seam) (a b : C.Corner) :
    Relation.EqvGen (C.glue retain) (C.cornerPoint a) (C.cornerPoint b) ↔
      Relation.EqvGen ((C.affineProjectionComplex A joined).glue retain)
        ((C.affineProjectionComplex A joined).cornerPoint a)
        ((C.affineProjectionComplex A joined).cornerPoint b) := by
  constructor
  · exact C.affineProjection_eqvGen A joined retain
  · intro related
    have inverse := C.affineProjection_inverse_eqvGen A joined retain related
    change Relation.EqvGen (C.glue retain)
      (C.affineProjectionInverseTotal A joined (C.affineProjectionTotal A joined (C.cornerPoint a)))
      (C.affineProjectionInverseTotal A joined (C.affineProjectionTotal A joined (C.cornerPoint b)))
      at inverse
    simpa only [C.affineProjectionInverseTotal_apply A joined] using inverse

/-- A projection changes the metric but retains each actual original corner class. -/
def affineProjectionVertexEquiv (retain : Set C.Seam) :
    C.Vertex retain ≃ (C.affineProjectionComplex A joined).Vertex retain :=
  Quotient.congr (Equiv.refl _) (C.affineProjection_corner_related_iff A joined retain)

@[simp] theorem affineProjectionVertexEquiv_ofCorner (retain : Set C.Seam) (c : C.Corner) :
    C.affineProjectionVertexEquiv A joined retain (C.vertexOfCorner retain c) =
      (C.affineProjectionComplex A joined).vertexOfCorner retain c := rfl

end Unfoldings.TriangleComplex
