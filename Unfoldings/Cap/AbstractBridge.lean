module

public import Unfoldings.Cap.SimpleEdgeUnfolding

/-! Proof translations for the independent geometric cap abstract. -/

@[expose] public section

noncomputable section

namespace Unfoldings.CapAbstractBridge

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- Translate ordinary corner coordinates and edge-pair labels into the implementation. -/
def meshComplex {Seam : Type v} [Fintype Seam]
    (vertex : Face → Fin 3 → Plane)
    (nondegenerate : ∀ f, orient (vertex f 0) (vertex f 1) (vertex f 2) ≠ 0)
    (first last : Seam → Face × Fin 3) (distinct : ∀ s, first s ≠ last s)
    (identify : ∀ s,
      (Triangle.mk (vertex (first s).1) (nondegenerate (first s).1)).Edge (first s).2 ≃ᵢ
      (Triangle.mk (vertex (last s).1) (nondegenerate (last s).1)).Edge (last s).2)
    (unique : ∀ s t, first s = first t ∨ first s = last t ∨
      last s = first t ∨ last s = last t → s = t) : TriangleComplex.{u, v} Face where
  triangle f := ⟨vertex f, nondegenerate f⟩
  Seam := Seam
  left s := ⟨(first s).1, (first s).2⟩
  right s := ⟨(last s).1, (last s).2⟩
  distinct s equal := distinct s (congrArg (fun e : EdgeRef Face => (e.face, e.edge)) equal)
  identify := identify
  unique s t shared := unique s t (by
    rcases shared with first | first | last | last
    · exact Or.inl (congrArg (fun e : EdgeRef Face => (e.face, e.edge)) first)
    · exact Or.inr (Or.inl (congrArg (fun e : EdgeRef Face => (e.face, e.edge)) first))
    · exact Or.inr (Or.inr (Or.inl
        (congrArg (fun e : EdgeRef Face => (e.face, e.edge)) last)))
    · exact Or.inr (Or.inr (Or.inr
        (congrArg (fun e : EdgeRef Face => (e.face, e.edge)) last))))

/-- Ordinary face/corner pairs give the same boundary-edge condition. -/
theorem boundary_edge_pair (e : EdgeRef Face) :
    C.IsBoundaryEdge Set.univ e ↔ ¬ ∃ s,
      (e.face, e.edge) = ((C.left s).face, (C.left s).edge) ∨
        (e.face, e.edge) = ((C.right s).face, (C.right s).edge) := by
  have pair_injective : Function.Injective (fun e : EdgeRef Face => (e.face, e.edge)) := by
    rintro ⟨f, i⟩ ⟨g, j⟩ equal
    cases equal
    rfl
  simp only [TriangleComplex.IsBoundaryEdge, TriangleComplex.Incident,
    Set.mem_univ, true_and, pair_injective.eq_iff]

/-- Raw finite-face geometric data gives exactly the implementation cap hypotheses. -/
def capOfGeometricData (F : SpatialFolding C) (normal : Face → Space)
    (unit : ∀ f, ‖normal f‖ = 1) (upward : ∀ f, 0 < normal f 2)
    (tangent : ∀ f x, inner ℝ (normal f) ((F.place f).linear x) = 0)
    (supporting : ∀ f (p : C.Total),
      inner ℝ (normal f) (F.place p.1 p.2.val - F.place f 0) ≤ 0)
    (projection : ∀ p q : C.Total,
      Cap.horizontal (F.place p.1 p.2.val) = Cap.horizontal (F.place q.1 q.2.val) →
        Relation.EqvGen (C.glue Set.univ) p q)
    (convex : Convex ℝ (Cap.horizontal '' F.surface))
    (interior_nonempty : (interior (Cap.horizontal '' F.surface)).Nonempty)
    (rim : ∀ bank : C.BoundaryBank Set.univ,
      ∀ x : (C.triangle bank.val.face).Edge bank.val.edge, F.place bank.val.face x.val 2 = 0)
    (above : ∀ f i, 0 ≤ F.place f ((C.triangle f).vertex i) 2) : ConvexCap C where
  folding := F
  normal := normal
  normal_unit := unit
  normal_upward := upward
  normal_tangent := tangent
  supporting f g x := supporting f ⟨g, x⟩
  projection_injective := by
    intro x y same
    obtain ⟨p, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
    obtain ⟨q, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) y
    exact (C.point_eq_iff Set.univ p q).mpr (projection p q same)
  convex_projection := convex
  interior_projection := interior_nonempty
  rim_horizontal := rim
  corners_above := above

/-- Expand the proved net into quotient topology, rigid placements, and a polygonal loop. -/
theorem unfolding_output (K : ConvexCap C) (U : K.SimpleEdgeUnfolding) :
    ∃ retain : Set C.Seam,
      Nonempty (C.SeamQuotient retain ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
      ∃ place : Face → Plane ≃ᵃⁱ[ℝ] Plane,
        (∀ p q : C.Total, place p.1 p.2.val = place q.1 q.2.val ↔
          Relation.EqvGen (C.glue retain) p q) ∧
        ((∃ n : ℕ, ∃ a b : Fin n → Plane,
          frontier (⋃ f, place f '' (C.triangle f).carrier) =
            ⋃ i, segment ℝ (a i) (b i)) ∧
          ∃ loop : ℝ → Plane, ContinuousOn loop (Set.Icc 0 1) ∧ loop 0 = loop 1 ∧
            Set.InjOn loop (Set.Ico 0 1) ∧
              loop '' Set.Icc 0 1 = frontier (⋃ f, place f '' (C.triangle f).carrier)) := by
  classical
  refine ⟨U.retain, ⟨(C.realizationHomeomorph U.retain).trans U.disk⟩,
    U.development.place, ?_, ?_⟩
  · intro p q
    have equality : U.development.place p.1 p.2.val = U.development.place q.1 q.2.val ↔
        MetricGluing.point C.Cell (C.glue U.retain) p =
          MetricGluing.point C.Cell (C.glue U.retain) q :=
      ⟨fun same => U.injective same, fun same => congrArg U.development.toPlane same⟩
    exact equality.trans (C.point_eq_iff U.retain p q)
  · have footprint : (⋃ f, U.development.place f '' (C.triangle f).carrier) = U.footprint := by
      ext z
      constructor
      · intro member
        obtain ⟨f, x, hx, rfl⟩ := Set.mem_iUnion.mp member
        exact ⟨C.faceMap U.retain f ⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue U.retain) x
        exact Set.mem_iUnion.mpr ⟨f, x.val, x.property, rfl⟩
    rw [footprint]
    let := Fintype.ofFinite (C.BoundaryBank U.retain)
    let e := Fintype.equivFin (C.BoundaryBank U.retain)
    let a (i : Fin (Fintype.card (C.BoundaryBank U.retain))) :=
      U.development.toPlane (C.vertexPoint U.retain
        ((C.boundaryGraph U.retain).left (e.symm i)).val)
    let b (i : Fin (Fintype.card (C.BoundaryBank U.retain))) :=
      U.development.toPlane (C.vertexPoint U.retain
        ((C.boundaryGraph U.retain).right (e.symm i)).val)
    refine ⟨⟨_, a, b, ?_⟩, ?_⟩
    · rw [U.frontier_eq_segments]
      ext z
      constructor
      · intro member
        obtain ⟨bank, member⟩ := Set.mem_iUnion.mp member
        refine Set.mem_iUnion.mpr ⟨e bank, ?_⟩
        simpa only [a, b, e.symm_apply_apply] using member
      · intro member
        obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
        exact Set.mem_iUnion.mpr ⟨e.symm i, member⟩
    · obtain ⟨loop, properties, image⟩ := U.frontier_isJordanCurve
      exact ⟨loop, properties.continuousOn, properties.closes, properties.injOn, image⟩

end Unfoldings.CapAbstractBridge
