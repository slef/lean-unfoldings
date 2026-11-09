module

public import Unfoldings.Complex
public import Unfoldings.Geometry.Edge
public import Unfoldings.Topology.FiniteClasses
public import Unfoldings.Metric.Barrier

/-! Finite seam classes for full-edge paired triangle complexes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A corner with its original face tag. -/
def IsVertex (a : C.Total) : Prop := (C.triangle a.1).IsVertex a.2.val

theorem finite_vertices : {a : C.Total | C.IsVertex a}.Finite := by
  let corner : Face × Fin 3 → C.Total := fun p =>
    ⟨p.1, ⟨(C.triangle p.1).vertex p.2, (C.triangle p.1).vertex_mem p.2⟩⟩
  apply (Set.finite_range corner).subset
  rintro ⟨f, x⟩ ⟨i, hi⟩
  exact ⟨(f, i), by dsimp [corner]; congr⟩

/-- A tagged point lies on a specified local edge. -/
def OnEdge (e : EdgeRef Face) (a : C.Total) : Prop :=
  a.1 = e.face ∧ a.2.val ∈ (C.triangle e.face).edge e.edge

theorem onEdge_unique {a : C.Total} (regular : ¬ C.IsVertex a) {e f : EdgeRef Face}
    (he : C.OnEdge e a) (hf : C.OnEdge f a) : e = f := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, e⟩ := e
  obtain ⟨k, f⟩ := f
  obtain ⟨rfl, he⟩ := he
  obtain ⟨rfl, hf⟩ := hf
  by_cases same : e = f
  · subst f
    rfl
  · exact (regular ((C.triangle i).isVertex_of_mem_edges same he hf)).elim

/-- The tagged version of an edge point, before quotienting. -/
def edgePoint (e : EdgeRef Face) (x : (C.triangle e.face).Edge e.edge) : C.Total :=
  ⟨e.face, (C.triangle e.face).edgeMap e.edge x⟩

theorem edgePoint_onEdge (e : EdgeRef Face) (x : (C.triangle e.face).Edge e.edge) :
    C.OnEdge e (C.edgePoint e x) := ⟨rfl, x.property⟩

theorem edgePoint_injective (e : EdgeRef Face) : Function.Injective (C.edgePoint e) := by
  intro x y equal
  exact Subtype.ext (congrArg (fun p : C.Total => p.2.val) equal)

/-- False selects the left side of a seam, true selects the right side. -/
def seamSide (s : C.Seam) : Bool → EdgeRef Face
  | false => C.left s
  | true => C.right s

/-- The inverse edge isometry is used when traversing a seam from its right bank. -/
def across (s : C.Seam) (side : Bool) :
    (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge ≃ᵢ
      (C.triangle (C.seamSide s (!side)).face).Edge (C.seamSide s (!side)).edge := by
  cases side
  · exact C.identify s
  · exact (C.identify s).symm

/-- Unique edge pairing makes the seam and its side determined by a local edge. -/
theorem seamSide_injective : Function.Injective (fun p : C.Seam × Bool => C.seamSide p.1 p.2) := by
  intro p q equal
  obtain ⟨s, side⟩ := p
  obtain ⟨t, side'⟩ := q
  have same : s = t := by
    apply C.unique s t
    cases side <;> cases side'
    · exact Or.inl equal
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr (Or.inl equal))
    · exact Or.inr (Or.inr (Or.inr equal))
  subst t
  congr 1
  cases side <;> cases side'
  · rfl
  · exact (C.distinct s equal).elim
  · exact (C.distinct s equal.symm).elim
  · rfl

/-- An undirected seam crossing, recording its source side. -/
def Crosses (retain : Set C.Seam) (a b : C.Total) : Prop :=
  ∃ s ∈ retain, ∃ side, ∃ x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge,
    a = C.edgePoint (C.seamSide s side) x ∧
      b = C.edgePoint (C.seamSide s (!side)) (C.across s side x)

theorem crosses_iff (retain : Set C.Seam) (a b : C.Total) :
    C.Crosses retain a b ↔ C.glue retain a b ∨ C.glue retain b a := by
  constructor
  · rintro ⟨s, hs, side, x, rfl, rfl⟩
    cases side
    · exact Or.inl ⟨s, hs, x, rfl, rfl⟩
    · apply Or.inr
      refine ⟨s, hs, (C.identify s).symm x, rfl, ?_⟩
      change C.edgePoint (C.right s) x = C.edgePoint (C.right s)
        (C.identify s ((C.identify s).symm x))
      exact congrArg (C.edgePoint (C.right s)) ((C.identify s).apply_symm_apply x).symm
  · rintro (⟨s, hs, x, rfl, rfl⟩ | ⟨s, hs, x, rfl, rfl⟩)
    · exact ⟨s, hs, false, x, rfl, rfl⟩
    · refine ⟨s, hs, true, C.identify s x, rfl, ?_⟩
      change C.edgePoint (C.left s) x = C.edgePoint (C.left s)
        ((C.identify s).symm (C.identify s x))
      exact congrArg (C.edgePoint (C.left s)) ((C.identify s).symm_apply_apply x).symm

theorem crosses_preserves_vertex {retain : Set C.Seam} {a b : C.Total}
    (crossing : C.Crosses retain a b) : C.IsVertex a ↔ C.IsVertex b := by
  obtain ⟨s, hs, side, x, rfl, rfl⟩ := crossing
  exact ((C.triangle (C.seamSide s side).face).edge_isometry_isVertex_iff
    (C.triangle (C.seamSide s (!side)).face) _ _ (C.across s side) x).symm

/-- Every nonvertex point has at most one undirected retained-seam neighbor. -/
theorem crosses_unique {retain : Set C.Seam} {a b c : C.Total} (regular : ¬ C.IsVertex a)
    (left : C.Crosses retain a b) (right : C.Crosses retain a c) : b = c := by
  obtain ⟨s, hs, side, x, ha, hb⟩ := left
  obtain ⟨t, ht, side', y, ha', hc⟩ := right
  have edge_equal := C.onEdge_unique regular
    (ha ▸ C.edgePoint_onEdge (C.seamSide s side) x)
    (ha' ▸ C.edgePoint_onEdge (C.seamSide t side') y)
  have sides_equal := C.seamSide_injective (a₁ := (s, side)) (a₂ := (t, side')) edge_equal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj sides_equal
  have point_equal : x = y := C.edgePoint_injective _ (ha.symm.trans ha')
  subst y
  exact hb.trans hc.symm

theorem glue_preserves_vertex (retain : Set C.Seam) (a b : C.Total) (h : C.glue retain a b) :
    C.IsVertex a ↔ C.IsVertex b :=
  C.crosses_preserves_vertex ((C.crosses_iff retain a b).mpr (Or.inl h))

/-- Away from corners, finite seam chains add only the unique directly paired point. -/
theorem eqvGen_iff_of_regular (retain : Set C.Seam) {a b : C.Total} (regular : ¬ C.IsVertex a) :
    Relation.EqvGen (C.glue retain) a b ↔ a = b ∨ C.Crosses retain a b := by
  constructor
  · intro related
    have unique : ∀ x, ¬ C.IsVertex x → ∀ {y z},
        (C.glue retain x y ∨ C.glue retain y x) →
        (C.glue retain x z ∨ C.glue retain z x) → y = z := by
      intro x hx y z hy hz
      exact C.crosses_unique hx ((C.crosses_iff retain x y).mpr hy)
        ((C.crosses_iff retain x z).mpr hz)
    rcases eq_or_adj_of_eqvGen_of_unique_neighbors (C.glue_preserves_vertex retain)
      unique related regular with equal | adjacent
    · exact Or.inl equal
    · exact Or.inr ((C.crosses_iff retain a b).mpr adjacent)
  · rintro (rfl | crossing)
    · exact Relation.EqvGen.refl _
    · rcases (C.crosses_iff retain a b).mp crossing with forward | backward
      · exact Relation.EqvGen.rel _ _ forward
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ backward)

/-- All declared seam classes are finite, including classes of identified corners. -/
theorem finite_class (retain : Set C.Seam) (a : C.Total) :
    {b | Relation.EqvGen (C.glue retain) a b}.Finite := by
  apply finite_eqvGen_class_of_finite_exceptional C.finite_vertices (C.glue_preserves_vertex retain)
  intro x regular y z hy hz
  exact C.crosses_unique regular ((C.crosses_iff retain x y).mpr hy)
    ((C.crosses_iff retain x z).mpr hz)

/-- The part of a declared seam class in any original triangle is finite. -/
theorem finite_classIn (retain : Set C.Seam) (a : C.Total) (f : Face) :
    (MetricGluing.classIn C.Cell (C.glue retain) a f).Finite := by
  exact Set.Finite.preimage (f := fun x : C.Cell f => (⟨f, x⟩ : C.Total))
    (fun _ _ _ _ equal => eq_of_heq (Sigma.mk.inj equal).2) (C.finite_class retain a)

end Unfoldings.TriangleComplex
