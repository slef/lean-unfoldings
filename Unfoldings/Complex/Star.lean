module

public import Unfoldings.Complex.Excision
public import Unfoldings.Complex.Germs
public import Unfoldings.Complex.Angles

/-!
# Vertex stars with their actual local metric

Keep precisely the retained seams incident to a chosen vertex. This preserves
its complete corner class, total angle, and a whole small intrinsic ball. The
remaining original triangles may still exist as separate distant components;
they cannot affect that local ball.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Retained seams whose edge image contains the chosen metric vertex. -/
def vertexStarSeams (retain : Set C.Seam) (v : C.Vertex retain) : Set C.Seam :=
  {s | s ∈ retain ∧ ∃ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    C.faceMap retain (C.left s).face ((C.triangle (C.left s).face).edgeMap (C.left s).edge x) =
      C.vertexPoint retain v}

theorem vertexStarSeams_subset (retain : Set C.Seam) (v : C.Vertex retain) :
    C.vertexStarSeams retain v ⊆ retain := fun _ h => h.1

theorem vertexStar_keeps_incident (retain : Set C.Seam) (c : C.Corner) :
    ∀ s ∈ retain, C.SeamIncident retain (C.cornerPoint c) s →
      s ∈ C.vertexStarSeams retain (C.vertexOfCorner retain c) := by
  rintro s kept ⟨x, related⟩
  exact ⟨kept, x, ((C.point_eq_iff retain _ _).mpr related).symm⟩

/-- Vertex-star membership can be read directly from the endpoint germ classes. -/
theorem mem_vertexStarSeams_iff (retain : Set C.Seam) (v : C.Vertex retain) (s : C.Seam) :
    s ∈ C.vertexStarSeams retain v ↔ s ∈ retain ∧ ∃ b : Bool,
      C.vertexOfCorner retain (C.germOfEndpoint (C.left s) b).1 = v := by
  constructor
  · rintro ⟨kept, x, equal⟩
    have vertex : (C.triangle (C.left s).face).IsVertex x :=
      (C.mem_range_vertexPoint_iff retain (C.edgePoint (C.left s) x)).mp ⟨v, equal.symm⟩
    obtain ⟨b, rfl⟩ := (C.triangle (C.left s).face).exists_endpoint (C.left s).edge x vertex
    refine ⟨kept, b, C.vertexPoint_injective retain ?_⟩
    rw [C.vertexPoint_vertexOfCorner, C.cornerPoint_germOfEndpoint]
    exact equal
  · rintro ⟨kept, b, equal⟩
    refine ⟨kept, (C.triangle (C.left s).face).endpoint (C.left s).edge b, ?_⟩
    have mapped := congrArg (C.vertexPoint retain) equal
    rw [C.vertexPoint_vertexOfCorner, C.cornerPoint_germOfEndpoint] at mapped
    exact mapped

/-- Distant seam cuts do not split the central vertex class. -/
theorem eqvGen_vertexStar_iff (retain : Set C.Seam) (c : C.Corner) (a : C.Total) :
    Relation.EqvGen (C.glue (C.vertexStarSeams retain (C.vertexOfCorner retain c)))
      (C.cornerPoint c) a ↔ Relation.EqvGen (C.glue retain) (C.cornerPoint c) a :=
  C.eqvGen_iff_of_kept_incident (C.vertexStarSeams_subset retain _) (C.cornerPoint c)
    (C.vertexStar_keeps_incident retain c) a

theorem vertexOfCorner_vertexStar_eq_iff (retain : Set C.Seam) (c d : C.Corner) :
    C.vertexOfCorner (C.vertexStarSeams retain (C.vertexOfCorner retain c)) c =
      C.vertexOfCorner (C.vertexStarSeams retain (C.vertexOfCorner retain c)) d ↔
    C.vertexOfCorner retain c = C.vertexOfCorner retain d := by
  rw [C.vertexOfCorner_eq_iff, C.vertexOfCorner_eq_iff, C.eqvGen_vertexStar_iff]

/-- The original corner contributions are exactly the corner contributions in its isolated star. -/
theorem totalAngle_vertexStar (retain : Set C.Seam) (c : C.Corner) :
    C.totalAngle (C.vertexStarSeams retain (C.vertexOfCorner retain c))
      (C.vertexOfCorner (C.vertexStarSeams retain (C.vertexOfCorner retain c)) c) =
        C.totalAngle retain (C.vertexOfCorner retain c) := by
  classical
  simp only [totalAngle]
  apply Finset.sum_congr rfl
  intro d _
  have same := C.vertexOfCorner_vertexStar_eq_iff retain c d
  rw [eq_comm] at same
  simpa only [eq_comm] using congrArg (fun p : Prop =>
    if p then (C.triangle d.1).cornerAngle d.2 else 0) (propext same)

/-- The central vertex has a unique preimage when restoring the distant star cuts. -/
theorem vertexForgetCuts_vertexStar_eq_iff (retain : Set C.Seam) (c : C.Corner)
    (v : C.Vertex (C.vertexStarSeams retain (C.vertexOfCorner retain c))) :
    C.vertexForgetCuts (C.vertexStarSeams_subset retain _) v = C.vertexOfCorner retain c ↔
      v = C.vertexOfCorner (C.vertexStarSeams retain (C.vertexOfCorner retain c)) c := by
  constructor
  · intro equal
    obtain ⟨d, rfl⟩ := C.vertexOfCorner_surjective _ v
    exact ((C.vertexOfCorner_vertexStar_eq_iff retain c d).mpr equal.symm).symm
  · rintro rfl
    exact C.vertexForgetCuts_vertexOfCorner _ c

/-- The star construction yields the same whole small metric ball via cut restoration. -/
theorem exists_vertexStarChart (retain : Set C.Seam) (c : C.Corner) :
    Nonempty (MetricGluing.ForgetChart C.Cell
      (C.glue_mono (C.vertexStarSeams_subset retain (C.vertexOfCorner retain c)))
      (C.cornerPoint c)) :=
  C.exists_localForgetChart (C.vertexStarSeams_subset retain _) (C.cornerPoint c)
    (C.vertexStar_keeps_incident retain c)

end Unfoldings.TriangleComplex
