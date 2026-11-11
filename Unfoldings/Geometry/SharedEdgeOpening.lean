module

public import Unfoldings.Geometry.HingeConverse

/-! Common geometric edge sets suffice for the strict opposite-side criterion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Equal actual edge carriers supply the identity edge isometry. -/
def sharedEdgeIdentification (T U : Triangle) (e f : Fin 3) (same : T.edge e = U.edge f) :
    T.Edge e ≃ᵢ U.Edge f where
  toEquiv :=
    { toFun x := ⟨x.val, same ▸ x.property⟩
      invFun y := ⟨y.val, same.symm ▸ y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  isometry_toFun := fun _ _ => rfl

/-- Disjoint genuine triangles sharing a whole geometric edge lie strictly on opposite sides. -/
theorem opposite_of_shared_edge (T U : Triangle) (e f : Fin 3) (same : T.edge e = U.edge f)
    (disjoint : Disjoint (interior T.carrier) (interior U.carrier)) :
    orient (T.vertex e) (T.vertex (next e)) (T.opposite e) *
      orient (T.vertex e) (T.vertex (next e)) (U.opposite f) < 0 :=
  T.opposite_of_disjoint U e f (T.sharedEdgeIdentification U e f same) (fun _ => rfl) disjoint

end Unfoldings.Triangle
