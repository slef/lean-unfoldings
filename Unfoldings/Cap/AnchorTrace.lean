module

public import Unfoldings.Cap.RimAnchor
public import Unfoldings.Cap.SectionTraceTurns
public import Unfoldings.Geometry.RayAvoidance

/-!
# Constructed vertex-avoiding sections from one common rim anchor

For every original face choose an interior target outside the finitely many
lines through the anchor and original corners. The constructed section trace
therefore starts in the anchor's fixed face and crosses original seams away
from original vertices. No regular-route certificate is input.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RimAnchor

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} (A : K.RimAnchor)

/-- Every actual original face admits a target whose complete section line avoids all corners. -/
theorem exists_regular_target (f : Face) :
    ∃ q ∈ interior (K.projectedTriangle f).carrier, q ≠ A.point ∧
      ∀ t : ℝ, ∀ g i, AffineMap.lineMap A.point q t ≠ (K.projectedTriangle g).vertex i := by
  obtain ⟨q, inside, regular⟩ := exists_open_endpoint_line_avoids A.point
    (fun i : Face × Fin 3 => (K.projectedTriangle i.1).vertex i.2)
    (fun i => A.point_ne_corner i.1 i.2) isOpen_interior (K.projectedTriangle f).interior_nonempty
  have different : q ≠ A.point := by
    intro equal
    have nonzero := regular (f, 0)
    rw [equal, orient_self_left] at nonzero
    exact nonzero rfl
  exact ⟨q, inside, different, fun t g i => lineMap_ne_of_orient_ne_zero (regular (g, i)) t⟩

/-- The first labeled original face is the same for every section leaving the anchor. -/
theorem trace_first_face {q : Plane} (T : K.SectionFaceTrace A.point q) :
    T.face 0 = A.bank.val.face := by
  apply A.point_unique_face
  have member := T.point_mem_face_first 0
  have start_point : T.point (0 : Fin (T.turns + 1)).castSucc = A.point := by
    simp only [SectionFaceTrace.point, Fin.castSucc_zero, T.start]
    exact AffineMap.lineMap_apply_zero _ _
  rwa [start_point] at member

/-- An interior target forces the final labeled face to be the requested original face. -/
theorem trace_last_face {f : Face} {q : Plane}
    (inside : q ∈ interior (K.projectedTriangle f).carrier)
    (T : K.SectionFaceTrace A.point q) : T.face (Fin.last T.turns) = f := by
  have member := T.point_mem_face_last (Fin.last T.turns)
  have end_point : T.point (Fin.last T.turns).succ = q := by
    rw [Fin.succ_last]
    change AffineMap.lineMap A.point q (T.time (Fin.last (T.turns + 1)) : ℝ) = q
    rw [T.finish]
    exact AffineMap.lineMap_apply_one _ _
  rw [end_point] at member
  exact K.projected_face_unique_of_interior inside member

/-- Construct an actual finite trace to the requested face with vertex avoidance proved. -/
theorem exists_regular_face_trace (f : Face) :
    ∃ q ∈ interior (K.projectedTriangle f).carrier, ∃ T : K.SectionFaceTrace A.point q,
      q ≠ A.point ∧ T.face 0 = A.bank.val.face ∧
        ∀ t : ℝ, ∀ g i, AffineMap.lineMap A.point q t ≠ (K.projectedTriangle g).vertex i := by
  obtain ⟨q, inside, different, regular⟩ := A.exists_regular_target f
  have footprint : q ∈ K.footprint := K.footprint_eq_union_projectedTriangles.symm ▸
    Set.mem_iUnion.mpr ⟨f, interior_subset inside⟩
  let T := K.sectionFaceTrace A.point_mem_footprint footprint
  exact ⟨q, inside, T, different, A.trace_first_face T, regular⟩

/-- Both endpoint face labels and complete original-vertex avoidance are derived. -/
theorem exists_regular_face_trace_to (f : Face) :
    ∃ q ∈ interior (K.projectedTriangle f).carrier, ∃ T : K.SectionFaceTrace A.point q,
      q ≠ A.point ∧ T.face 0 = A.bank.val.face ∧ T.face (Fin.last T.turns) = f ∧
        ∀ t : ℝ, ∀ g i, AffineMap.lineMap A.point q t ≠ (K.projectedTriangle g).vertex i := by
  obtain ⟨q, inside, T, different, first, regular⟩ := A.exists_regular_face_trace f
  exact ⟨q, inside, T, different, first, A.trace_last_face inside T, regular⟩

end Unfoldings.ConvexCap.RimAnchor
