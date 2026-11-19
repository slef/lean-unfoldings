module

public import Unfoldings.Complex.Folding
public import Unfoldings.Complex.BoundaryQuotient

/-! Away from the physical removed edges, a cut boundary bank was already an original bank. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (cuts : Set Space)
  (removed : ∀ s, s ∉ retain → ∀ z : (C.triangle (C.left s).face).Edge (C.left s).edge,
    F.place (C.left s).face z.val ∈ cuts)

include removed

/-- A physical point outside the removed edges cannot lie on a newly created bank. -/
theorem boundaryBank_original_of_outside (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (outside : F.place bank.val.face x.val ∉ cuts) : C.IsBoundaryEdge Set.univ bank.val := by
  rintro ⟨s, _, incident⟩
  have cut : s ∉ retain := fun kept => bank.property ⟨s, kept, incident⟩
  obtain ⟨edge, boundary⟩ := bank
  rcases incident with first | last
  · change edge = C.left s at first
    subst edge
    exact outside (removed s cut x)
  · change edge = C.right s at last
    subst edge
    let y := (C.identify s).symm x
    have physical : F.place (C.left s).face y.val = F.place (C.right s).face x.val :=
      (F.joined s y).trans (congrArg (fun z => F.place (C.right s).face z.val)
        ((C.identify s).apply_symm_apply x))
    exact outside (physical ▸ removed s cut y)

end Unfoldings.SpatialFolding
