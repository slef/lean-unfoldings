module

public import Unfoldings.Complex.Vertices
public import Unfoldings.Geometry.Endpoints

/-!
# The two edge germs at each triangle corner

False follows the outgoing local edge and true follows the incoming local edge.
Turning within a corner exchanges these two germs. Retained seam identifications
give a second, partial pairing, including endpoint reversals and self-pairings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem cornerPoint_injective : Function.Injective C.cornerPoint := by
  rintro ⟨f, i⟩ ⟨g, j⟩ equal
  have faces : f = g := congrArg (fun a : C.Total => a.1) equal
  subst g
  have corners : i = j := (C.triangle f).vertex_injective
    (congrArg (fun a : C.Total => a.2.val) equal)
  subst j
  rfl

theorem exists_cornerPoint_of_isVertex {a : C.Total} (vertex : C.IsVertex a) :
    ∃ c, C.cornerPoint c = a := by
  obtain ⟨f, x⟩ := a
  obtain ⟨i, equal⟩ := vertex
  refine ⟨(f, i), ?_⟩
  exact congrArg (Sigma.mk f) (Subtype.ext equal)

/-- Each original corner has two incident edge germs. -/
abbrev Germ (_C : TriangleComplex.{u, v} Face) := (Face × Fin 3) × Bool

def germEdge (p : C.Germ) : EdgeRef Face :=
  ⟨p.1.1, if p.2 then Triangle.next (Triangle.next p.1.2) else p.1.2⟩

/-- Encode an endpoint of a local edge as the germ at its corresponding corner. -/
def germOfEndpoint (e : EdgeRef Face) (b : Bool) : C.Germ :=
  ((e.face, if b then Triangle.next e.edge else e.edge), b)

@[simp] theorem germEdge_germOfEndpoint (e : EdgeRef Face) (b : Bool) :
    C.germEdge (C.germOfEndpoint e b) = e := by
  obtain ⟨f, i⟩ := e
  cases b <;> fin_cases i <;> rfl

@[simp] theorem germOfEndpoint_germEdge (p : C.Germ) :
    C.germOfEndpoint (C.germEdge p) p.2 = p := by
  obtain ⟨⟨f, i⟩, b⟩ := p
  cases b <;> fin_cases i <;> rfl

@[simp] theorem germOfEndpoint_side (e : EdgeRef Face) (b : Bool) :
    (C.germOfEndpoint e b).2 = b := rfl

theorem cornerPoint_germOfEndpoint (e : EdgeRef Face) (b : Bool) :
    C.cornerPoint (C.germOfEndpoint e b).1 =
      C.edgePoint e ((C.triangle e.face).endpoint e.edge b) := by
  cases b <;> rfl

/-- Exchange the two sides of one corner, without crossing a seam. -/
def turnGerm (p : C.Germ) : C.Germ := (p.1, !p.2)

theorem turnGerm_involutive : Function.Involutive C.turnGerm := by
  rintro ⟨c, b⟩
  cases b <;> rfl

theorem turnGerm_ne (p : C.Germ) : C.turnGerm p ≠ p := by
  obtain ⟨c, b⟩ := p
  intro equal
  have impossible := congrArg Prod.snd equal
  cases b <;> cases impossible

theorem germ_corner_eq_iff (p q : C.Germ) : p.1 = q.1 ↔ p = q ∨ p = C.turnGerm q := by
  obtain ⟨c, b⟩ := p
  obtain ⟨d, e⟩ := q
  cases b <;> cases e <;> simp [turnGerm]

/-- Endpoint transport in the chosen direction of a seam; reverse transport is its inverse. -/
def acrossEndpoint (s : C.Seam) : Bool → (Bool ≃ Bool)
  | false => (C.triangle (C.left s).face).endpointEquiv (C.triangle (C.right s).face)
      (C.left s).edge (C.right s).edge (C.identify s)
  | true => ((C.triangle (C.left s).face).endpointEquiv (C.triangle (C.right s).face)
      (C.left s).edge (C.right s).edge (C.identify s)).symm

theorem acrossEndpoint_inverse (s : C.Seam) (side b : Bool) :
    C.acrossEndpoint s (!side) (C.acrossEndpoint s side b) = b := by
  cases side
  · exact Equiv.symm_apply_apply _ _
  · exact Equiv.apply_symm_apply _ _

theorem endpoint_acrossEndpoint (s : C.Seam) (side b : Bool) :
    (C.triangle (C.seamSide s (!side)).face).endpoint (C.seamSide s (!side)).edge
      (C.acrossEndpoint s side b) = C.across s side
        ((C.triangle (C.seamSide s side).face).endpoint (C.seamSide s side).edge b) := by
  cases side
  · exact Triangle.endpoint_endpointEquiv _ _ _ _ _ b
  · change (C.triangle (C.left s).face).endpoint (C.left s).edge
      (((C.triangle (C.left s).face).endpointEquiv (C.triangle (C.right s).face)
        (C.left s).edge (C.right s).edge (C.identify s)).symm b) = _
    rw [← Triangle.endpointEquiv_symm]
    exact Triangle.endpoint_endpointEquiv _ _ _ _ _ b

/-- An undirected retained-seam crossing of corner edge germs. -/
def GermCrosses (retain : Set C.Seam) (p q : C.Germ) : Prop :=
  ∃ s ∈ retain, ∃ side b,
    p = C.germOfEndpoint (C.seamSide s side) b ∧
      q = C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side b)

theorem GermCrosses.symm {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) : C.GermCrosses retain q p := by
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  refine ⟨s, kept, !side, C.acrossEndpoint s side b, rfl, ?_⟩
  rw [Bool.not_not, C.acrossEndpoint_inverse]

theorem GermCrosses.unique {retain : Set C.Seam} {p q r : C.Germ}
    (left : C.GermCrosses retain p q) (right : C.GermCrosses retain p r) : q = r := by
  obtain ⟨s, kept, side, b, hp, rfl⟩ := left
  obtain ⟨t, kept', side', c, hp', rfl⟩ := right
  have edges : C.seamSide s side = C.seamSide t side' := by
    simpa only [C.germEdge_germOfEndpoint] using congrArg C.germEdge (hp.symm.trans hp')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (C.seamSide_injective (a₁ := (s, side)) (a₂ := (t, side')) edges)
  have endpoints : b = c := congrArg Prod.snd (hp.symm.trans hp')
  rw [endpoints]

theorem GermCrosses.ne {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) : p ≠ q := by
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  intro equal
  have edges := congrArg C.germEdge equal
  simp only [C.germEdge_germOfEndpoint] at edges
  cases side
  · exact C.distinct s edges
  · exact C.distinct s edges.symm

/-- Germ crossings induce the actual point identifications in the cut metric. -/
theorem GermCrosses.crosses {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) :
    C.Crosses retain (C.cornerPoint p.1) (C.cornerPoint q.1) := by
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  rw [C.cornerPoint_germOfEndpoint, C.cornerPoint_germOfEndpoint, C.endpoint_acrossEndpoint]
  exact ⟨s, kept, side, _, rfl, rfl⟩

theorem GermCrosses.vertex_eq {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) :
    C.vertexOfCorner retain p.1 = C.vertexOfCorner retain q.1 := by
  apply (C.vertexOfCorner_eq_iff retain _ _).mpr
  rcases (C.crosses_iff retain _ _).mp crossing.crosses with forward | backward
  · exact Relation.EqvGen.rel _ _ forward
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ backward)

end Unfoldings.TriangleComplex
