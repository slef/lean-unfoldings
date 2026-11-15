module

public import Unfoldings.Metric.ClosedSeams
public import Unfoldings.Metric.IsometricCells
public import Unfoldings.Metric.FiniteCompleteCover

/-! Exact complete gluings along arbitrary finite closed physical seam pieces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I X : Type*} [Finite I] [MetricSpace X] (cells : I → Set X)

/-- Selected physical seam pieces. Individual seams may be bounded or unbounded;
only these declared pieces are glued, even when other spatial points coincide. -/
structure PhysicalSeams where
  carrier : I → I → Set X
  closed : ∀ i j, IsClosed (carrier i j)
  subset_left : ∀ i j, carrier i j ⊆ cells i
  subset_right : ∀ i j, carrier i j ⊆ cells j

namespace PhysicalSeams

variable {cells} (S : PhysicalSeams cells)

/-- Actual physical seams form a finite closed isometric seam system. -/
def closedSeams : ClosedSeams (fun i => cells i) where
  Seam := I × I
  Domain := fun p => S.carrier p.1 p.2
  left := Prod.fst
  right := Prod.snd
  toLeft := fun p x => ⟨x.val, S.subset_left p.1 p.2 x.property⟩
  toRight := fun p x => ⟨x.val, S.subset_right p.1 p.2 x.property⟩
  left_isometry := fun _ _ _ => rfl
  right_isometry := fun _ _ _ => rfl
  left_closed := by
    intro p
    have equality : Set.range (fun x : S.carrier p.1 p.2 =>
        (⟨x.val, S.subset_left p.1 p.2 x.property⟩ : cells p.1)) =
        {x : cells p.1 | x.val ∈ S.carrier p.1 p.2} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro member
        exact ⟨⟨x.val, member⟩, rfl⟩
    rw [equality]
    exact (S.closed p.1 p.2).preimage continuous_subtype_val
  right_closed := by
    intro p
    have equality : Set.range (fun x : S.carrier p.1 p.2 =>
        (⟨x.val, S.subset_right p.1 p.2 x.property⟩ : cells p.2)) =
        {x : cells p.2 | x.val ∈ S.carrier p.1 p.2} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro member
        exact ⟨⟨x.val, member⟩, rfl⟩
    rw [equality]
    exact (S.closed p.1 p.2).preimage continuous_subtype_val

/-- The declared seam relation, with no automatic identification of other coincidences. -/
abbrev relation := S.closedSeams.relation

/-- Following actual seam chains preserves the original spatial point. -/
theorem physical_eq_of_eqvGen {a b : Total (fun i => cells i)}
    (related : Relation.EqvGen S.relation a b) : a.2.val = b.2.val := by
  induction related with
  | rel a b joined =>
    obtain ⟨p, x, rfl, rfl⟩ := joined
    rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first last => exact first.trans last

/-- Each seam class has at most one original point in any given physical cell. -/
theorem classIn_subsingleton (a : Total (fun i => cells i)) (i : I) :
    (classIn (fun j => cells j) S.relation a i).Subsingleton := by
  intro x hx y hy
  apply Subtype.ext
  exact (S.physical_eq_of_eqvGen hx).symm.trans (S.physical_eq_of_eqvGen hy)

/-- No extra zero-distance identifications arise, even on unbounded seam pieces. -/
theorem exact : Exact (fun i => cells i) S.relation :=
  S.closedSeams.exact_of_finite_classes (fun a i => (S.classIn_subsingleton a i).finite)

/-- Global physical coordinates prevent shortcuts inside any original cell. -/
theorem of_isometry (i : I) : Isometry (of (fun j => cells j) S.relation i) := by
  apply of_isometry_of_compatible (fun j => cells j) S.relation
    (fun _ x => x.val) (fun _ => isometry_subtype_coe)
  intro a b related
  exact S.physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ related)

/-- Spatial folding retains distinct cut-bank copies while mapping them to their original points. -/
def fold : Realization (fun i => cells i) S.relation → X :=
  lift (fun i => cells i) S.relation (fun _ x => x.val)
    (fun _ => isometry_subtype_coe.lipschitzWith)
    (fun _ _ joined => S.physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ joined))

@[simp] theorem fold_of (i : I) (x : cells i) :
    S.fold (of (fun j => cells j) S.relation i x) = x.val := rfl

theorem fold_lipschitz : LipschitzWith 1 S.fold :=
  lift_lipschitz (fun i => cells i) S.relation _ _ _

/-- Restoring any declared physical seam pieces can only shorten distances. -/
theorem relation_mono {T : PhysicalSeams cells}
    (included : ∀ i j, S.carrier i j ⊆ T.carrier i j) :
    ∀ a b, S.relation a b → T.relation a b := by
  rintro a b ⟨p, x, rfl, rfl⟩
  exact ⟨p, ⟨x.val, included p.1 p.2 x.property⟩, rfl, rfl⟩

variable [CompleteSpace X]

/-- Finite complete physical cells remain complete after any such selection of closed seams. -/
theorem completeSpace_realization (closed : ∀ i, IsClosed (cells i)) :
    CompleteSpace (Realization (fun i => cells i) S.relation) := by
  let complete (i : I) : CompleteSpace (cells i) := (closed i).isComplete.completeSpace_coe
  apply completeSpace_of_finite_isometric_cover (fun i => cells i)
    (of (fun i => cells i) S.relation) S.of_isometry
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => cells i) S.relation x
  exact ⟨i, p, rfl⟩

/-- The physical cell quotient has its actual route-metric topology, without compactness. -/
theorem isClosedMap_point (closed : ∀ i, IsClosed (cells i)) :
    IsClosedMap (point (fun i => cells i) S.relation) := by
  let complete (i : I) : CompleteSpace (cells i) := (closed i).isComplete.completeSpace_coe
  intro t closed_t
  have equality : point (fun i => cells i) S.relation '' t =
      ⋃ i, of (fun j => cells j) S.relation i '' ((@Sigma.mk I (fun i => cells i) i) ⁻¹' t) := by
    ext x
    constructor
    · rintro ⟨⟨i, p⟩, member, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, p, member, rfl⟩
    · intro member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      obtain ⟨p, hp, equal⟩ := hi
      exact ⟨⟨i, p⟩, hp, equal⟩
  rw [equality]
  exact isClosed_iUnion_of_finite (fun i => (S.of_isometry i).isClosedEmbedding.isClosedMap _
    (closed_t.preimage continuous_sigmaMk))

/-- Finite complete physical-cell covers give the original quotient topology. -/
theorem isQuotientMap_point (closed : ∀ i, IsClosed (cells i)) :
    Topology.IsQuotientMap (point (fun i => cells i) S.relation) :=
  (S.isClosedMap_point closed).isQuotientMap (continuous_point _ _) (point_surjective _ _)

theorem isClosedMap_toMetric (closed : ∀ i, IsClosed (cells i)) :
    IsClosedMap (toMetric (fun i => cells i) S.relation) := by
  intro t closed_t
  have equality : point (fun i => cells i) S.relation ''
      (seamPoint (fun i => cells i) S.relation ⁻¹' t) =
        toMetric (fun i => cells i) S.relation '' t := by
    ext x
    constructor
    · rintro ⟨p, hp, equal⟩
      exact ⟨seamPoint (fun i => cells i) S.relation p, hp, equal⟩
    · rintro ⟨q, hq, equal⟩
      obtain ⟨p, rfl⟩ := Quot.exists_rep q
      exact ⟨p, hq, equal⟩
  rw [← equality]
  exact S.isClosedMap_point closed _ (closed_t.preimage continuous_quot_mk)

/-- Seam topology and actual metric topology agree without compact cells. -/
def seamHomeomorph (closed : ∀ i, IsClosed (cells i)) :
    SeamQuotient (fun i => cells i) S.relation ≃ₜ Realization (fun i => cells i) S.relation :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (toMetric (fun i => cells i) S.relation)
      ⟨(exact_iff_toMetric_injective _ _).mp S.exact, toMetric_surjective _ _⟩)
    (continuous_toMetric _ _) (S.isClosedMap_toMetric closed)

@[simp] theorem seamHomeomorph_seamPoint (closed : ∀ i, IsClosed (cells i))
    (x : Total (fun i => cells i)) :
    S.seamHomeomorph closed (seamPoint (fun i => cells i) S.relation x) =
      point (fun i => cells i) S.relation x := rfl

end PhysicalSeams
end Unfoldings.MetricGluing
