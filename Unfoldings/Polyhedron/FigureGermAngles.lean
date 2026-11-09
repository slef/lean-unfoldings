module

public import Unfoldings.Polyhedron.FigureGerms
public import Unfoldings.Geometry.RadialSliceAngles

/-!
# Genuine lateral angles of the actual figure edges

The spatial angle subtended by the endpoints of each figure edge is exactly
the original triangle corner angle. In particular these endpoints differ.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

theorem germPoint_apex_angle (p : C.LinkGerm Set.univ v) :
    EuclideanGeometry.angle (V.place (V.germPoint p))
        (F.toSpace Set.univ (C.vertexPoint Set.univ v))
        (V.place (V.germPoint (C.linkTurn Set.univ v p))) =
      (C.triangle p.val.1.1).cornerAngle p.val.1.2 := by
  rw [V.place_germPoint, V.place_germPoint]
  have left := V.supported (C.germFarCorner p.val) (F.linkGerm_far_ne_apex Set.univ v p)
  have right := V.supported (C.germFarCorner (C.linkTurn Set.univ v p).val)
    (F.linkGerm_far_ne_apex Set.univ v (C.linkTurn Set.univ v p))
  have normalized := angle_radialSlicePoint V.functional
    (F.toSpace Set.univ (C.vertexPoint Set.univ v)) (F.germFarPoint p.val)
    (F.germFarPoint (C.linkTurn Set.univ v p).val) V.level V.positive
    (V.positive.trans left) (V.positive.trans right)
  refine normalized.trans ?_
  rw [← F.linkGerm_apex Set.univ v p]
  obtain ⟨⟨⟨face, i⟩, side⟩, hp⟩ := p
  cases side
  · exact (F.place face).angle_map _ _ _
  · exact ((F.place face).angle_map _ _ _).trans (EuclideanGeometry.angle_comm _ _ _)

theorem place_germPoint_ne_apex (p : C.LinkGerm Set.univ v) :
    V.place (V.germPoint p) ≠ F.toSpace Set.univ (C.vertexPoint Set.univ v) := by
  rw [V.place_germPoint]
  exact radialSlicePoint_ne_origin V.functional _ V.level _
    (V.positive.trans (V.supported (C.germFarCorner p.val)
      (F.linkGerm_far_ne_apex Set.univ v p))).ne' V.positive

theorem germPoint_ne_turn (p : C.LinkGerm Set.univ v) :
    V.germPoint p ≠ V.germPoint (C.linkTurn Set.univ v p) := by
  intro equal
  have angle := V.germPoint_apex_angle p
  rw [← equal, EuclideanGeometry.angle_self_of_ne (V.place_germPoint_ne_apex p)] at angle
  exact (C.triangle p.val.1.1).cornerAngle_pos p.val.1.2 |>.ne' angle.symm

end Unfoldings.SpatialFolding.VertexFigure
