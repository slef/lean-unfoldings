module

public import Unfoldings.Polyhedron.FigureGerms
public import Unfoldings.Polyhedron.GermEdges

/-!
# Exact incidence of figure endpoints

The section misses every original spatial corner. Its germ points lift to
nonvertex points of their original local edges. Embeddedness therefore
identifies figure endpoints precisely for equal germs or seam mates.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)

theorem place_ne_spatial_corner (p : Plane) (c : C.Corner) :
    V.place p ≠ F.place c.1 ((C.triangle c.1).vertex c.2) := by
  intro equal
  have height := V.range_place.le ⟨p, rfl⟩
  change V.functional (V.place p - F.toSpace Set.univ (C.vertexPoint Set.univ v)) =
    V.level at height
  rw [equal] at height
  by_cases apex : F.place c.1 ((C.triangle c.1).vertex c.2) =
      F.toSpace Set.univ (C.vertexPoint Set.univ v)
  · rw [apex, sub_self, map_zero] at height
    exact V.positive.ne' height.symm
  · exact (V.supported c apex).ne height.symm

def germCoordinate (p : C.LinkGerm Set.univ v) : Plane :=
  AffineMap.lineMap ((C.triangle p.val.1.1).vertex p.val.1.2)
    ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2)
    (V.level / V.functional
      (F.germFarPoint p.val - F.toSpace Set.univ (C.vertexPoint Set.univ v)))

theorem place_germCoordinate (p : C.LinkGerm Set.univ v) :
    F.place p.val.1.1 (V.germCoordinate p) = V.place (V.germPoint p) := by
  rw [V.place_germPoint]
  change F.place p.val.1.1 (AffineMap.lineMap _ _ _) = _
  rw [F.place_lineMap, F.linkGerm_apex]
  rfl

theorem germCoordinate_mem_edge (p : C.LinkGerm Set.univ v) :
    V.germCoordinate p ∈ (C.triangle (C.germEdge p.val).face).edge
      (C.germEdge p.val).edge := by
  have height := V.supported (C.germFarCorner p.val) (F.linkGerm_far_ne_apex Set.univ v p)
  have positive := V.positive.trans height
  have parameter : V.level / V.functional
      (F.germFarPoint p.val - F.toSpace Set.univ (C.vertexPoint Set.univ v)) ∈
        Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg V.positive.le positive.le,
      (div_le_one positive).mpr height.le⟩
  have member := lineMap_mem_segment ℝ ((C.triangle p.val.1.1).vertex p.val.1.2)
    ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2) parameter
  change V.germCoordinate p ∈ segment ℝ _ _ at member
  obtain ⟨⟨⟨face, i⟩, side⟩, hp⟩ := p
  cases side
  · exact member
  · fin_cases i <;> exact (segment_symm ℝ _ _).subset member

theorem germCoordinate_mem_carrier (p : C.LinkGerm Set.univ v) :
    V.germCoordinate p ∈ (C.triangle p.val.1.1).carrier :=
  (C.triangle p.val.1.1).edge_subset _ (V.germCoordinate_mem_edge p)

theorem germCoordinate_not_vertex (p : C.LinkGerm Set.univ v) :
    ¬ (C.triangle p.val.1.1).IsVertex (V.germCoordinate p) := by
  rintro ⟨i, equal⟩
  apply V.place_ne_spatial_corner (V.germPoint p) (p.val.1.1, i)
  rw [← V.place_germCoordinate, equal]

theorem germPoint_eq_iff (embedded : F.IsEmbedded) (p q : C.LinkGerm Set.univ v) :
    V.germPoint p = V.germPoint q ↔ p = q ∨ C.linkMate Set.univ v p = q := by
  constructor
  · intro equal
    let a : C.Total := ⟨p.val.1.1, ⟨V.germCoordinate p, V.germCoordinate_mem_carrier p⟩⟩
    let b : C.Total := ⟨q.val.1.1, ⟨V.germCoordinate q, V.germCoordinate_mem_carrier q⟩⟩
    apply F.linkGerms_eq_or_mate_of_regular_spatial_point embedded
      (a := a) (b := b) (V.germCoordinate_not_vertex p)
      ⟨rfl, V.germCoordinate_mem_edge p⟩ ⟨rfl, V.germCoordinate_mem_edge q⟩
    change F.place p.val.1.1 (V.germCoordinate p) =
      F.place q.val.1.1 (V.germCoordinate q)
    rw [V.place_germCoordinate, V.place_germCoordinate, equal]
  · rintro (rfl | paired)
    · rfl
    · rw [← paired, V.germPoint_mate]

end Unfoldings.SpatialFolding.VertexFigure
