module

public import Unfoldings.Development.ClosedFaceSeparation
public import Unfoldings.Geometry.Hinge
public import Unfoldings.Geometry.SharedEdgeInterior
public import Unfoldings.Geometry.TriangleMotion

/-! A retained nonvertex hinge point cannot meet a foreign developed face or boundary copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem moved_seam_edges_eq (s : C.Seam) (kept : s ∈ retain) :
    ((C.triangle (C.left s).face).move (D.place (C.left s).face)).edge (C.left s).edge =
      ((C.triangle (C.right s).face).move (D.place (C.right s).face)).edge (C.right s).edge := by
  rw [Triangle.move_edge, Triangle.move_edge]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, member, rfl⟩
    let y : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨x, member⟩
    exact ⟨(C.identify s y).val, (C.identify s y).property, (D.joined s kept y).symm⟩
  · rintro _ ⟨x, member, rfl⟩
    let y : (C.triangle (C.right s).face).Edge (C.right s).edge := ⟨x, member⟩
    let z := (C.identify s).symm y
    refine ⟨z.val, z.property, ?_⟩
    exact (D.joined s kept z).trans
      (congrArg (fun w => D.place (C.right s).face w.val) ((C.identify s).apply_symm_apply y))

theorem retained_hinge_point_mem_interior_union (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x.val) :
    D.place (C.left s).face x.val ∈
      interior (D.faceImage (C.left s).face ∪ D.faceImage (C.right s).face) := by
  let T := (C.triangle (C.left s).face).move (D.place (C.left s).face)
  let U := (C.triangle (C.right s).face).move (D.place (C.right s).face)
  let y : T.Edge (C.left s).edge :=
    ((C.triangle (C.left s).face).moveEdge (D.place (C.left s).face) (C.left s).edge) x
  have nonvertex : ¬ T.IsVertex y.val := by
    rintro ⟨i, equal⟩
    exact regular ⟨i, (D.place (C.left s).face).injective equal⟩
  have disjoint : Disjoint (interior T.carrier) (interior U.carrier) := by
    simpa only [T, U, Triangle.move_carrier, faceImage] using D.hinge_nonoverlap s kept
  have inside := T.shared_edge_mem_interior_union U _ _ (D.moved_seam_edges_eq s kept)
    disjoint y nonvertex
  change D.place (C.left s).face x.val ∈ interior (T.carrier ∪ U.carrier) at inside
  simpa only [T, U, Triangle.move_carrier, faceImage] using inside

theorem Nonoverlapping.eq_faceMap_of_toPlane_eq_retained_hinge
    (nonoverlap : D.Nonoverlapping) (s : C.Seam) (kept : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x.val)
    (y : C.Realization retain) (same : D.toPlane y = D.place (C.left s).face x.val) :
    y = C.faceMap retain (C.left s).face ((C.triangle _).edgeMap _ x) := by
  obtain ⟨⟨g, z⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  change D.place g z.val = D.place (C.left s).face x.val at same
  by_cases first : g = (C.left s).face
  · subst g
    exact congrArg (C.faceMap retain (C.left s).face)
      (Subtype.ext ((D.place (C.left s).face).injective same))
  · by_cases last : g = (C.right s).face
    · subst g
      have coordinates : z.val = (C.identify s x).val :=
        (D.place (C.right s).face).injective (same.trans (D.joined s kept x))
      exact (congrArg (C.faceMap retain (C.right s).face) (Subtype.ext coordinates)).trans
        (C.seam_identified retain s kept x).symm
    · have separate := Nonoverlapping.interior_union_disjoint_closed_face D nonoverlap
        (Ne.symm first) (Ne.symm last)
      have inside := D.retained_hinge_point_mem_interior_union s kept x regular
      exact (Set.disjoint_left.mp separate inside ⟨z.val, z.property, same⟩).elim

end Unfoldings.FacewiseDevelopment
