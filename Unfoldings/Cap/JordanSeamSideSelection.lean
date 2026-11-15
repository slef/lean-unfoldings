module

public import Unfoldings.Cap.JordanOriginalBanks

/-! The actual bounded Jordan filling selects exactly one incident side of each original seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
/-- A genuine original edge on the respected curve has an actual selected incident face.
This derives an initial side alternative from the physical filling, rather than supplying one. -/
theorem jordan_seam_incident_selected (s : C.Seam)
    (on_curve : (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ J) :
    (C.left s).face ∈ K.jordanFaces J ∨ (C.right s).face ∈ K.jordanFaces J := by
  obtain ⟨x, regular⟩ := (C.triangle (C.left s).face).exists_edge_nonvertex (C.left s).edge
  let p := K.projectFace (C.left s).face x.val
  have on_edge : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
    rw [ConvexCap.projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩
  have domain : p ∈ PlanarTopology.closedJordanDomain J := by
    apply (show IsClosed (PlanarTopology.closedJordanDomain J) from
      isClosed_closure).frontier_subset
    rw [PlanarTopology.frontier_closedJordanDomain jordan]
    exact on_curve on_edge
  rw [K.jordanDomain_eq_projectedFace_union jordan contains avoids] at domain
  obtain ⟨f, selected, member⟩ := Set.mem_iUnion₂.mp domain
  rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨y, inside, coordinates⟩ := member
  have equal : C.faceMap Set.univ (C.left s).face ((C.triangle _).edgeMap (C.left s).edge x) =
      C.faceMap Set.univ f ⟨y, inside⟩ := K.projection_injective coordinates.symm
  have related := (C.faceMap_eq_iff Set.univ _ _ _ _).mp equal
  have regular' : ¬ C.IsVertex (C.edgePoint (C.left s) x) := regular
  have crossing : C.Crosses Set.univ (C.edgePoint (C.left s) x)
      (C.edgePoint (C.right s) (C.identify s x)) := ⟨s, Set.mem_univ _, false, x, rfl, rfl⟩
  rcases (C.eqvGen_iff_eq_or_neighbor regular' crossing).mp related with same | same
  · left
    have faces := congrArg Sigma.fst same
    change f = (C.left s).face at faces
    exact faces ▸ selected
  · right
    have faces := congrArg Sigma.fst same
    change f = (C.right s).face at faces
    exact faces ▸ selected

include jordan contains avoids in
open Classical in
/-- Both incident faces cannot be selected: their retained seam would contradict
that the physical curve is the actual boundary of its intrinsic Jordan disk. -/
theorem jordan_seam_not_both_selected (s : C.Seam)
    (on_curve : (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ J) :
    ¬ ((C.left s).face ∈ K.jordanFaces J ∧ (C.right s).face ∈ K.jordanFaces J) := by
  rintro ⟨first, last⟩
  have boundary := K.jordan_selected_edge_isBoundary jordan contains avoids
    ⟨(C.left s).face, first⟩ (C.left s).edge on_curve
  exact boundary ⟨⟨s, first, last⟩, Set.mem_univ _, Or.inl rfl⟩

include jordan contains avoids in
/-- The initial physical side is uniquely determined, though either original bank may be inside. -/
theorem jordan_seam_exactly_one_face (s : C.Seam)
    (on_curve : (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ J) :
    ((C.left s).face ∈ K.jordanFaces J ∧ (C.right s).face ∉ K.jordanFaces J) ∨
      ((C.right s).face ∈ K.jordanFaces J ∧ (C.left s).face ∉ K.jordanFaces J) := by
  have distinct := K.jordan_seam_not_both_selected jordan contains avoids s on_curve
  rcases K.jordan_seam_incident_selected jordan contains avoids s on_curve with first | last
  · exact Or.inl ⟨first, fun last => distinct ⟨first, last⟩⟩
  · exact Or.inr ⟨last, fun first => distinct ⟨first, last⟩⟩

end Unfoldings.ConvexCap
