module

public import Unfoldings.Examples.Tetrahedron.Complex
public import Unfoldings.Polyhedron.Convex

/-! Certify the actual tetrahedron as an embedded full-dimensional convex boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

theorem seam_points_related (s : Fin 6) (x : (triangle (left s).face).Cell)
    (y : (triangle (right s).face).Cell)
    (equal : placement (left s).face x.val = placement (right s).face y.val) :
    Relation.EqvGen (complex.glue Set.univ) ⟨(left s).face, x⟩ ⟨(right s).face, y⟩ := by
  have zero : (triangle (left s).face).coord
      (Triangle.next (Triangle.next (left s).edge)) x.val = 0 := by
    rw [← weight_corner_placement, opposite_label, equal, weight_omitted_placement]
  have on_edge := ((triangle (left s).face).mem_edge_iff (left s).edge x.val).mpr
    ⟨x.property, zero⟩
  let edge : (triangle (left s).face).Edge (left s).edge := ⟨x.val, on_edge⟩
  have right_equal : (identify s edge).val = y.val :=
    (placement (right s).face).injective ((identify_joined s edge).symm.trans equal)
  apply Relation.EqvGen.rel
  refine ⟨s, Set.mem_univ _, edge, rfl, ?_⟩
  exact congrArg (Sigma.mk (right s).face) (Subtype.ext right_equal.symm)

theorem points_related (f g : Fin 4) (x : (triangle f).Cell) (y : (triangle g).Cell)
    (equal : placement f x.val = placement g y.val) :
    Relation.EqvGen (complex.glue Set.univ) ⟨f, x⟩ ⟨g, y⟩ := by
  by_cases same : f = g
  · subst g
    have equal := (placement f).injective equal
    have cells : x = y := Subtype.ext equal
    subst y
    exact Relation.EqvGen.refl _
  · obtain ⟨s, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := face_pair f g same
    · exact seam_points_related s x y equal
    · exact (seam_points_related s y x equal.symm).symm

theorem embedded : folding.IsEmbedded := by
  rw [folding.isEmbedded_iff]
  rintro ⟨f, x⟩ ⟨g, y⟩ equal
  exact points_related f g x y equal

theorem vertexHull_eq : folding.vertexHull = hull := by
  unfold SpatialFolding.vertexHull hull
  congr 1
  ext p
  constructor
  · rintro ⟨⟨f, i⟩, equal⟩
    exact ⟨corner f i, (placement_vertex f i).symm.trans equal⟩
  · rintro ⟨i, rfl⟩
    let f : Fin 4 := if i = 0 then 1 else 0
    have different : i ≠ f := by
      dsimp [f]
      split_ifs with zero
      · exact zero ▸ (by decide : (0 : Fin 4) ≠ 1)
      · exact zero
    obtain ⟨j, equal⟩ := corner_surjective_away f i different
    exact ⟨(f, j), (placement_vertex f j).trans (congrArg vertex equal)⟩

theorem surface_eq : folding.surface = frontier folding.vertexHull := by
  rw [vertexHull_eq, frontier_hull]
  change (⋃ f, placement f '' (triangle f).carrier) = ⋃ f, facet f
  congr 1
  funext f
  exact placement_image_carrier f

theorem convexBoundary : folding.ConvexBoundary where
  embedded := embedded
  interior_nonempty := vertexHull_eq.symm ▸ hull_interior_nonempty
  boundary := surface_eq

end Unfoldings.Examples.Tetrahedron
