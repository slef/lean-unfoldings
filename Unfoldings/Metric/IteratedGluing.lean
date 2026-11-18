module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.MetricSpace.Isometry

/-! Gluing already glued pieces is isometric to gluing all original cells at once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w

variable {I : Type u} {J : I → Type v} (E : ∀ i, J i → Type w)
  [∀ i j, PseudoEMetricSpace (E i j)]
  (inner : ∀ i, Total (E i) → Total (E i) → Prop)
  (outer : Total (fun i => Realization (E i) (inner i)) →
    Total (fun i => Realization (E i) (inner i)) → Prop)

/-- Original cell tags retain both their piece and their local cell index. -/
abbrev NestedCell (ij : Σ i, J i) := E ij.1 ij.2

/-- Restore the tag of an original cell point in its already glued piece. -/
def nestedPoint (x : Total (NestedCell E)) :
    Total (fun i => Realization (E i) (inner i)) :=
  ⟨x.1.1, of (E x.1.1) (inner x.1.1) x.1.2 x.2⟩

/-- Keep original internal seams and add exactly the requested identifications between pieces. -/
inductive NestedGlue : Total (NestedCell E) → Total (NestedCell E) → Prop
  | inside (i : I) (x y : Total (E i)) (related : inner i x y) :
      NestedGlue ⟨⟨i, x.1⟩, x.2⟩ ⟨⟨i, y.1⟩, y.2⟩
  | between (x y : Total (NestedCell E))
      (related : outer (nestedPoint E inner x) (nestedPoint E inner y)) : NestedGlue x y

/-- Include a whole original metric piece in the single gluing of its underlying cells. -/
def pieceToNested (i : I) :
    Realization (E i) (inner i) → Realization (NestedCell E) (NestedGlue E inner outer) :=
  lift (E i) (inner i)
    (fun j x => of (NestedCell E) (NestedGlue E inner outer) ⟨i, j⟩ x)
    (fun j => of_lipschitz (NestedCell E) (NestedGlue E inner outer) ⟨i, j⟩)
    (fun x y related => point_eq_of_glue (NestedCell E) (NestedGlue.inside i x y related))

/-- Inclusion of an entire piece cannot increase intrinsic route distance. -/
theorem pieceToNested_lipschitz (i : I) : LipschitzWith 1 (pieceToNested E inner outer i) :=
  lift_lipschitz (E i) (inner i) _ _ _

/-- Every declared outer seam is an equality in the flattened metric realization. -/
theorem pieceToNested_compatible
    (x y : Total (fun i => Realization (E i) (inner i))) (related : outer x y) :
    pieceToNested E inner outer x.1 x.2 = pieceToNested E inner outer y.1 y.2 := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  obtain ⟨a, rfl⟩ := point_surjective (E i) (inner i) x
  obtain ⟨b, rfl⟩ := point_surjective (E j) (inner j) y
  exact point_eq_of_glue (NestedCell E) (NestedGlue.between
    ⟨⟨i, a.1⟩, a.2⟩ ⟨⟨j, b.1⟩, b.2⟩ related)

/-- Flatten the iterated metric construction without changing any original point. -/
def iteratedToNested :
    Realization (fun i => Realization (E i) (inner i)) outer →
      Realization (NestedCell E) (NestedGlue E inner outer) :=
  lift (fun i => Realization (E i) (inner i)) outer (pieceToNested E inner outer)
    (pieceToNested_lipschitz E inner outer) (pieceToNested_compatible E inner outer)

/-- Regroup original cells into their original metric pieces. -/
def nestedToIterated :
    Realization (NestedCell E) (NestedGlue E inner outer) →
      Realization (fun i => Realization (E i) (inner i)) outer :=
  lift (NestedCell E) (NestedGlue E inner outer)
    (fun ij x => of (fun i => Realization (E i) (inner i)) outer ij.1
      (of (E ij.1) (inner ij.1) ij.2 x))
    (fun ij => by
      have first := of_lipschitz (E ij.1) (inner ij.1) ij.2
      have second := of_lipschitz (fun i => Realization (E i) (inner i)) outer ij.1
      simpa only [one_mul, Function.comp_def] using second.comp first)
    (by
      intro x y related
      cases related with
      | inside i a b seam =>
        exact congrArg (of (fun i => Realization (E i) (inner i)) outer i)
          (point_eq_of_glue (E i) seam)
      | between a b seam => exact point_eq_of_glue _ seam)

/-- Both regrouping maps are nonexpanding for the actual route metrics. -/
theorem iteratedToNested_lipschitz : LipschitzWith 1 (iteratedToNested E inner outer) :=
  lift_lipschitz _ _ _ _ _

theorem nestedToIterated_lipschitz : LipschitzWith 1 (nestedToIterated E inner outer) :=
  lift_lipschitz _ _ _ _ _

/-- Flattening and regrouping keep every original cell point literally fixed. -/
theorem nested_leftInverse :
    Function.LeftInverse (iteratedToNested E inner outer) (nestedToIterated E inner outer) := by
  intro x
  obtain ⟨⟨⟨i, j⟩, p⟩, rfl⟩ := point_surjective (NestedCell E) (NestedGlue E inner outer) x
  rfl

theorem nested_rightInverse :
    Function.RightInverse (iteratedToNested E inner outer) (nestedToIterated E inner outer) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => Realization (E i) (inner i)) outer x
  obtain ⟨⟨j, q⟩, rfl⟩ := point_surjective (E i) (inner i) p
  rfl

/-- Exact metric associativity lets actual gap pieces be assembled first, then flattened
into their original finite convex cells. No exactness, compactness or flatness is assumed. -/
def nestedIsometryEquiv :
    Realization (NestedCell E) (NestedGlue E inner outer) ≃ᵢ
      Realization (fun i => Realization (E i) (inner i)) outer where
  toFun := nestedToIterated E inner outer
  invFun := iteratedToNested E inner outer
  left_inv := nested_leftInverse E inner outer
  right_inv := nested_rightInverse E inner outer
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using nestedToIterated_lipschitz E inner outer x y
    · have bound := iteratedToNested_lipschitz E inner outer
        (nestedToIterated E inner outer x) (nestedToIterated E inner outer y)
      simpa only [nested_leftInverse E inner outer x, nested_leftInverse E inner outer y,
        ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
