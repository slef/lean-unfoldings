module

public import Unfoldings.Complex.Links

/-! The connected components of corner germs are exactly the actual cut vertex classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- One move inside a corner or across its retained edge. -/
def GermStep (retain : Set C.Seam) (p q : C.Germ) : Prop :=
  q = C.turnGerm p ∨ q = C.mateGerm retain p

theorem germStep_vertex_eq {retain : Set C.Seam} {p q : C.Germ}
    (step : C.GermStep retain p q) : C.vertexOfCorner retain p.1 = C.vertexOfCorner retain q.1 := by
  rcases step with rfl | rfl
  · rfl
  · exact (C.mateGerm_vertex_eq retain p).symm

theorem germs_related_of_corner_eq (retain : Set C.Seam) {p q : C.Germ} (same : p.1 = q.1) :
    Relation.EqvGen (C.GermStep retain) p q := by
  rcases (C.germ_corner_eq_iff p q).mp same with rfl | opposite
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl opposite))

theorem exists_germCrosses_of_glue (retain : Set C.Seam) (c d : C.Corner)
    (joined : C.glue retain (C.cornerPoint c) (C.cornerPoint d)) :
    ∃ p q : C.Germ, p.1 = c ∧ q.1 = d ∧ C.GermCrosses retain p q := by
  obtain ⟨s, kept, x, hc, hd⟩ := joined
  have vertex : (C.triangle (C.left s).face).IsVertex x := by
    have original := C.isVertex_cornerPoint c
    rw [hc] at original
    exact original
  obtain ⟨b, rfl⟩ := (C.triangle (C.left s).face).exists_endpoint (C.left s).edge x vertex
  let p := C.germOfEndpoint (C.left s) b
  let q := C.germOfEndpoint (C.right s) (C.acrossEndpoint s false b)
  have left : C.cornerPoint p.1 = C.cornerPoint c :=
    (C.cornerPoint_germOfEndpoint (C.left s) b).trans hc.symm
  have right : C.cornerPoint q.1 = C.cornerPoint d := by
    exact (C.cornerPoint_germOfEndpoint (C.right s) _).trans
      ((congrArg (C.edgePoint (C.right s)) (C.endpoint_acrossEndpoint s false b)).trans hd.symm)
  exact ⟨p, q, C.cornerPoint_injective left, C.cornerPoint_injective right,
    s, kept, false, b, rfl, rfl⟩

/-- No extra link components are hidden inside a retained vertex equivalence class. -/
theorem germs_related_iff_vertex_eq (retain : Set C.Seam) (p q : C.Germ) :
    Relation.EqvGen (C.GermStep retain) p q ↔
      C.vertexOfCorner retain p.1 = C.vertexOfCorner retain q.1 := by
  constructor
  · intro related
    induction related with
    | rel p q h => exact C.germStep_vertex_eq h
    | refl p => rfl
    | symm p q h ih => exact ih.symm
    | trans p q r hpq hqr ih₁ ih₂ => exact ih₁.trans ih₂
  · intro equal
    have related := (C.vertexOfCorner_eq_iff retain p.1 q.1).mp equal
    have lift {a b : C.Total} (h : Relation.EqvGen (C.glue retain) a b) :
        ∀ p q : C.Germ, C.cornerPoint p.1 = a → C.cornerPoint q.1 = b →
          Relation.EqvGen (C.GermStep retain) p q := by
      induction h with
      | rel a b h =>
        intro p q hp hq
        obtain ⟨r, s, hr, hs, cross⟩ := C.exists_germCrosses_of_glue retain p.1 q.1
          (by rw [hp, hq]; exact h)
        exact Relation.EqvGen.trans _ _ _ (C.germs_related_of_corner_eq retain hr.symm)
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ (Or.inr (C.mateGerm_of_crossing cross).symm))
            (C.germs_related_of_corner_eq retain hs))
      | refl a =>
        intro p q hp hq
        exact C.germs_related_of_corner_eq retain (C.cornerPoint_injective (hp.trans hq.symm))
      | symm a b h ih =>
        intro p q hp hq
        exact Relation.EqvGen.symm _ _ (ih q p hq hp)
      | trans a b c hab hbc ih₁ ih₂ =>
        intro p q hp hq
        have vertex : C.IsVertex b := (C.eqvGen_preserves_vertex retain hab).mp
          (hp ▸ C.isVertex_cornerPoint p.1)
        obtain ⟨corner, hcorner⟩ := C.exists_cornerPoint_of_isVertex vertex
        let middle : C.Germ := (corner, false)
        exact Relation.EqvGen.trans _ _ _ (ih₁ p middle hp hcorner) (ih₂ middle q hcorner hq)
    exact lift related p q rfl rfl

/-- A link move is turning or seam transport restricted to one metric vertex. -/
def LinkStep (retain : Set C.Seam) (v : C.Vertex retain)
    (p q : C.LinkGerm retain v) : Prop :=
  q = C.linkTurn retain v p ∨ q = C.linkMate retain v p

theorem linkGerms_related (retain : Set C.Seam) (v : C.Vertex retain)
    (p q : C.LinkGerm retain v) : Relation.EqvGen (C.LinkStep retain v) p q := by
  have related := (C.germs_related_iff_vertex_eq retain p.val q.val).mpr
    (p.property.trans q.property.symm)
  have lift {a b : C.Germ} (h : Relation.EqvGen (C.GermStep retain) a b) :
      ∀ ha : C.vertexOfCorner retain a.1 = v, ∀ hb : C.vertexOfCorner retain b.1 = v,
        Relation.EqvGen (C.LinkStep retain v) ⟨a, ha⟩ ⟨b, hb⟩ := by
    induction h with
    | rel a b h =>
      intro ha hb
      apply Relation.EqvGen.rel
      rcases h with rfl | rfl
      · exact Or.inl (Subtype.ext rfl)
      · exact Or.inr (Subtype.ext rfl)
    | refl a =>
      intro ha hb
      exact Relation.EqvGen.refl _
    | symm a b h ih =>
      intro ha hb
      exact Relation.EqvGen.symm _ _ (ih hb ha)
    | trans a b c hab hbc ih₁ ih₂ =>
      intro ha hc
      have hb : C.vertexOfCorner retain b.1 = v :=
        ((C.germs_related_iff_vertex_eq retain a b).mp hab).symm.trans ha
      exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hc)
  exact lift related p.property q.property

end Unfoldings.TriangleComplex
