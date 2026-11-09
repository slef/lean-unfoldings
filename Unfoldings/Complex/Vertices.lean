module

public import Unfoldings.Complex.Exact
public import Unfoldings.Boundary

/-!
# Vertex copies in cut realizations

Vertices are equivalence classes of tagged triangle corners under exactly the
retained seams. Their canonical images in the intrinsic metric are injective.
Removing seams can split a vertex; restoring seams maps its copies together.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Corners retain both their original face and their local corner index. -/
abbrev Corner (_C : TriangleComplex.{u, v} Face) := Face × Fin 3

/-- A tagged triangle corner before any gluing. -/
def cornerPoint (c : C.Corner) : C.Total :=
  ⟨c.1, ⟨(C.triangle c.1).vertex c.2, (C.triangle c.1).vertex_mem c.2⟩⟩

theorem isVertex_cornerPoint (c : C.Corner) : C.IsVertex (C.cornerPoint c) := ⟨c.2, rfl⟩

theorem eqvGen_preserves_vertex (retain : Set C.Seam) {a b : C.Total}
    (related : Relation.EqvGen (C.glue retain) a b) : C.IsVertex a ↔ C.IsVertex b := by
  induction related with
  | rel a b h => exact C.glue_preserves_vertex retain a b h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- Declared corner equivalence uses finite retained-seam chains. -/
def vertexSetoid (retain : Set C.Seam) : Setoid C.Corner where
  r c d := Relation.EqvGen (C.glue retain) (C.cornerPoint c) (C.cornerPoint d)
  iseqv := ⟨fun _ => Relation.EqvGen.refl _, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩

/-- The distinct vertex copies of the completed cut metric. -/
def Vertex (retain : Set C.Seam) := Quotient (C.vertexSetoid retain)

instance (retain : Set C.Seam) : Finite (C.Vertex retain) := inferInstanceAs
  (Finite (Quotient (C.vertexSetoid retain)))

instance (retain : Set C.Seam) : Fintype (C.Vertex retain) := Fintype.ofFinite _

def vertexOfCorner (retain : Set C.Seam) (c : C.Corner) : C.Vertex retain :=
  Quotient.mk (C.vertexSetoid retain) c

theorem vertexOfCorner_eq_iff (retain : Set C.Seam) (c d : C.Corner) :
    C.vertexOfCorner retain c = C.vertexOfCorner retain d ↔
      Relation.EqvGen (C.glue retain) (C.cornerPoint c) (C.cornerPoint d) := Quotient.eq

theorem vertexOfCorner_surjective (retain : Set C.Seam) :
    Function.Surjective (C.vertexOfCorner retain) := Quotient.mk_surjective

/-- Vertices map into the actual metric realization, rather than an unrelated vertex set. -/
def vertexPoint (retain : Set C.Seam) : C.Vertex retain → C.Realization retain :=
  Quotient.lift (fun c => MetricGluing.point C.Cell (C.glue retain) (C.cornerPoint c))
    (fun _ _ related => (C.point_eq_iff retain _ _).mpr related)

@[simp] theorem vertexPoint_vertexOfCorner (retain : Set C.Seam) (c : C.Corner) :
    C.vertexPoint retain (C.vertexOfCorner retain c) =
      MetricGluing.point C.Cell (C.glue retain) (C.cornerPoint c) := rfl

theorem vertexPoint_injective (retain : Set C.Seam) :
    Function.Injective (C.vertexPoint retain) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      intro equal
      exact Quotient.sound ((C.point_eq_iff retain _ _).mp equal)

/-- A tagged point maps to a metric vertex exactly when it was an original corner. -/
theorem mem_range_vertexPoint_iff (retain : Set C.Seam) (a : C.Total) :
    MetricGluing.point C.Cell (C.glue retain) a ∈ Set.range (C.vertexPoint retain) ↔
      C.IsVertex a := by
  constructor
  · rintro ⟨v, equal⟩
    obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain v
    exact (C.eqvGen_preserves_vertex retain ((C.point_eq_iff retain _ _).mp equal)).mp
      (C.isVertex_cornerPoint c)
  · obtain ⟨f, x⟩ := a
    rintro ⟨i, equal⟩
    have coordinate : x = ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩ :=
      Subtype.ext equal.symm
    subst x
    exact ⟨C.vertexOfCorner retain (f, i), rfl⟩

/-- Restoring seams identifies exactly the corresponding classes of corner copies. -/
def vertexForgetCuts {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain') :
    C.Vertex retain → C.Vertex retain' :=
  Quotient.map id (fun _ _ related => related.mono (C.glue_mono inclusion))

@[simp] theorem vertexForgetCuts_vertexOfCorner {retain retain' : Set C.Seam}
    (inclusion : retain ⊆ retain') (c : C.Corner) :
    C.vertexForgetCuts inclusion (C.vertexOfCorner retain c) = C.vertexOfCorner retain' c := rfl

theorem vertexForgetCuts_surjective {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain') :
    Function.Surjective (C.vertexForgetCuts inclusion) := by
  intro v
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain' v
  exact ⟨C.vertexOfCorner retain c, rfl⟩

@[simp] theorem vertexPoint_vertexForgetCuts {retain retain' : Set C.Seam}
    (inclusion : retain ⊆ retain') (v : C.Vertex retain) :
    C.vertexPoint retain' (C.vertexForgetCuts inclusion v) =
      C.forgetCuts inclusion (C.vertexPoint retain v) := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain v
  exact (C.forgetCuts_faceMap inclusion c.1
    ⟨(C.triangle c.1).vertex c.2, (C.triangle c.1).vertex_mem c.2⟩).symm

/-- Boundary incidence refers to the endpoints of the actual unpaired banks. -/
def IsBoundaryVertex (retain : Set C.Seam) (v : C.Vertex retain) : Prop :=
  ∃ e : EdgeRef Face, C.IsBoundaryEdge retain e ∧
    (v = C.vertexOfCorner retain (e.face, e.edge) ∨
      v = C.vertexOfCorner retain (e.face, Triangle.next e.edge))

theorem bank_start_isBoundaryVertex (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    C.IsBoundaryVertex retain (C.vertexOfCorner retain (bank.val.face, bank.val.edge)) :=
  ⟨bank.val, bank.property, Or.inl rfl⟩

theorem bank_finish_isBoundaryVertex (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    C.IsBoundaryVertex retain
      (C.vertexOfCorner retain (bank.val.face, Triangle.next bank.val.edge)) :=
  ⟨bank.val, bank.property, Or.inr rfl⟩

end Unfoldings.TriangleComplex
