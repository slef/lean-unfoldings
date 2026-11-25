module

public import Unfoldings.Roof.ProjectionContour
public import Unfoldings.Roof.SharpLinkFans
public import Unfoldings.Complex.RestoredLinkChain

/-! Each actual bank keeps its projected side through the saved fan; a seam mate faces the other side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedGermRay_orient {w : C.Vertex Set.univ} (p : C.LinkGerm Set.univ w) :
    orient 0 (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ w p)) = K.projectedGermOrientation p.val := by
  have apex := K.projectedGerm_apex p
  unfold projectedGermRay
  rw [← apex]
  change orient 0 (_ - _) (_ - _) = orient _ _ _
  simp only [projectedTriangle, Triangle.affineImage_vertex, projectFace,
    SpatialFolding.germFarPoint, orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
  rfl

@[simp] theorem projectedGermOrientation_turn (p : C.Germ) :
    K.projectedGermOrientation (C.turnGerm p) = -K.projectedGermOrientation p := by
  obtain ⟨corner, side⟩ := p
  cases side <;>
    simp only [projectedGermOrientation, TriangleComplex.turnGerm, Bool.not_false, Bool.not_true]
  all_goals unfold orient; ring

/-- The two occurrences of a projected seam face opposite sides of its directed line. -/
theorem projectedGermOrientation_mate_mul_neg (p : C.Germ)
    (internal : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p)) :
    K.projectedGermOrientation (C.mateGerm Set.univ p) * K.projectedGermOrientation p < 0 := by
  let w := C.vertexOfCorner Set.univ p.1
  let x : C.LinkGerm Set.univ w := ⟨p, rfl⟩
  let y := C.linkMate Set.univ w x
  let xt := C.linkTurn Set.univ w x
  let yt := C.linkTurn Set.univ w y
  have same_ray := K.projectedGermRay_mate x
  change K.projectedGermRay y = K.projectedGermRay x at same_ray
  have different : x.val.1.1 ≠ y.val.1.1 := by
    change p.1.1 ≠ (C.mateGerm Set.univ p).1.1
    obtain ⟨q, crosses⟩ := (C.exists_germCrosses_iff Set.univ p).mpr internal
    rw [C.mateGerm_of_crossing crosses]
    obtain ⟨s, _, side, flag, rfl, rfl⟩ := crosses
    cases side <;> cases flag
    · exact K.folding.incident_faces_ne s
    · exact K.folding.incident_faces_ne s
    · exact Ne.symm (K.folding.incident_faces_ne s)
    · exact Ne.symm (K.folding.incident_faces_ne s)
  have separated : Disjoint
      (strictRayCone (K.projectedGermRay xt) (K.projectedGermRay x))
      (strictRayCone (K.projectedGermRay x) (K.projectedGermRay yt)) := by
    rw [strictRayCone_comm _ (K.projectedGermRay x), ← same_ray]
    change Disjoint (strictRayCone (K.projectedGermRay y) (K.projectedGermRay xt))
      (strictRayCone (K.projectedGermRay y) (K.projectedGermRay yt))
    have left_cone : strictRayCone (K.projectedGermRay y) (K.projectedGermRay xt) =
        strictRayCone (K.projectedGermRay x) (K.projectedGermRay xt) := by rw [same_ray]
    rw [left_cone, K.projectedGermRay_cone x, K.projectedGermRay_cone y]
    exact (K.projectedTriangle x.val.1.1).disjoint_cornerDirections (K.projectedTriangle y.val.1.1)
      x.val.1.2 y.val.1.2
      ((K.projectedGerm_apex x).trans (K.projectedGerm_apex y).symm)
      (K.projectedTriangles_nonoverlapping different)
  have x_area := K.projectedGermRay_orient x
  have y_area := K.projectedGermRay_orient y
  change orient 0 (K.projectedGermRay x) (K.projectedGermRay xt) = K.projectedGermOrientation p at x_area
  change orient 0 (K.projectedGermRay y) (K.projectedGermRay yt) =
    K.projectedGermOrientation (C.mateGerm Set.univ p) at y_area
  rw [same_ray] at y_area
  have opposite : orient 0 (K.projectedGermRay xt) (K.projectedGermRay x) =
      -K.projectedGermOrientation p := by
    rw [← x_area]
    simp only [orient, PiLp.zero_apply, sub_zero]
    ring
  have product := orient_mul_pos_of_disjoint_strictRayCones
    (show orient 0 (K.projectedGermRay xt) (K.projectedGermRay x) ≠ 0 by
      rw [opposite]; exact neg_ne_zero.mpr (K.projectedGermOrientation_ne_zero _))
    (show orient 0 (K.projectedGermRay x) (K.projectedGermRay yt) ≠ 0 by
      rw [y_area]; exact K.projectedGermOrientation_ne_zero _) separated
  rw [opposite, y_area] at product
  rw [neg_mul, mul_comm (K.projectedGermOrientation p)] at product
  exact neg_pos.mp product

/-- A retained fan crosses each actual hinge with the same oriented corner sign. -/
theorem projected_linkChain_sign {retain : Set C.Seam} {w : C.Vertex retain} {n : ℕ}
    (c : (C.linkSystem retain w).Chain n) (i : Fin (n + 1)) :
    (0 < K.projectedGermOrientation (c.point i).val) ↔
      0 < K.projectedGermOrientation c.first.val := by
  refine Fin.induction Iff.rfl (fun j previous => ?_) i
  obtain ⟨s, _, side, flag, first, last⟩ := C.chain_next_crosses retain w c j
  have crossed : C.GermCrosses Set.univ (C.turnGerm (c.point j.castSucc).val) (c.point j.succ).val :=
    ⟨s, Set.mem_univ _, side, flag, first, last⟩
  have product := K.projectedGermOrientation_mate_mul_neg _
    ((C.exists_germCrosses_iff Set.univ _).mp ⟨_, crossed⟩)
  rw [C.mateGerm_of_crossing crossed, K.projectedGermOrientation_turn, mul_neg] at product
  exact (pos_iff_pos_of_mul_pos (neg_lt_zero.mp product)).trans previous

/-- The starting and ending germs of the same saved fan have opposite signs. -/
theorem projected_boundaryMate_negative_iff {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    K.projectedGermOrientation (C.boundaryMate retain p).val < 0 ↔
      0 < K.projectedGermOrientation p.val := by
  obtain ⟨n, c, first, last, _⟩ := C.exists_boundary_link retain p
  have terminal : C.turnGerm c.last.val = (C.boundaryMate retain p).val := last
  rw [← terminal, K.projectedGermOrientation_turn, neg_lt_zero]
  exact (K.projected_linkChain_sign c (Fin.last n)).trans
    (show (0 < K.projectedGermOrientation c.first.val) ↔ 0 < K.projectedGermOrientation p.val by
      rw [first])

/-- The directed original bank has one orientation all the way along the chain. -/
theorem projected_boundaryChain_sign {retain : Set C.Seam} {n : ℕ}
    (bank : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (0 < K.projectedGermOrientation (bank.point i).val) ↔
      0 < K.projectedGermOrientation bank.first.val := by
  refine Fin.induction Iff.rfl (fun j previous => ?_) i
  have equal := congrArg (C.boundaryMate retain) (bank.next j)
  change C.boundaryMate retain (C.boundaryMate retain (C.boundaryTurn retain (bank.point j.castSucc))) =
    C.boundaryMate retain (bank.point j.succ) at equal
  rw [C.boundaryMate_involutive] at equal
  have sign := (K.projected_boundaryMate_negative_iff (bank.point j.succ)).symm
  rw [← equal, K.projectedGermOrientation_boundaryTurn, neg_lt_zero] at sign
  exact sign.trans previous

end Unfoldings.ConvexRoof
