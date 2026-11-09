module

public import Unfoldings.Boundary
public import Unfoldings.Complex.Exact
public import Unfoldings.Topology.BoundaryQuotient

/-!
# Restoring triangle seams is a boundary-only quotient

The bank boundary is the union of the actual unpaired closed bank images.
This set includes endpoints and any original unpaired edges. No manifold
boundary identification is assumed. Exact seam chains prove that distinct
points identified by restoring seams must both lie on the bank boundary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

def bankBoundary (retain : Set C.Seam) : Set (C.Realization retain) :=
  ⋃ bank : C.BoundaryBank retain, Set.range (C.bankMap retain bank)

theorem bankMap_mem_bankBoundary (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge) :
    C.bankMap retain bank x ∈ C.bankBoundary retain :=
  Set.mem_iUnion.mpr ⟨bank, x, rfl⟩

theorem finite_boundaryBank (retain : Set C.Seam) : Finite (C.BoundaryBank retain) := by
  have injective : Function.Injective (fun e : EdgeRef Face => (e.face, e.edge)) := by
    rintro ⟨f, e⟩ ⟨g, d⟩ equal
    cases equal
    rfl
  let : Finite (EdgeRef Face) := Finite.of_injective _ injective
  infer_instance

theorem isCompact_bankBoundary (retain : Set C.Seam) : IsCompact (C.bankBoundary retain) := by
  let := C.finite_boundaryBank retain
  exact isCompact_iUnion (fun bank => isCompact_range (C.bankMap_lipschitz retain bank).continuous)

theorem isClosed_bankBoundary (retain : Set C.Seam) : IsClosed (C.bankBoundary retain) :=
  (C.isCompact_bankBoundary retain).isClosed

theorem forgetCuts_surjective {small large : Set C.Seam} (inclusion : small ⊆ large) :
    Function.Surjective (C.forgetCuts inclusion) := by
  intro x
  obtain ⟨a, image⟩ := MetricGluing.point_surjective C.Cell (C.glue large) x
  exact ⟨MetricGluing.point C.Cell (C.glue small) a, image⟩

theorem eq_or_bankBoundary_of_eqvGen {small large : Set C.Seam} {a b : C.Total}
    (related : Relation.EqvGen (C.glue large) a b) :
    MetricGluing.point C.Cell (C.glue small) a = MetricGluing.point C.Cell (C.glue small) b ∨
      (MetricGluing.point C.Cell (C.glue small) a ∈ C.bankBoundary small ∧
        MetricGluing.point C.Cell (C.glue small) b ∈ C.bankBoundary small) := by
  classical
  induction related with
  | rel a b related =>
    obtain ⟨s, _, x, rfl, rfl⟩ := related
    by_cases kept : s ∈ small
    · exact Or.inl (C.seam_identified small s kept x)
    · exact Or.inr ⟨C.bankMap_mem_bankBoundary small (C.leftBank small s kept) x,
        C.bankMap_mem_bankBoundary small (C.rightBank small s kept) (C.identify s x)⟩
  | refl a => exact Or.inl rfl
  | symm a b related ih =>
    exact ih.elim (fun equal => Or.inl equal.symm) (fun both => Or.inr ⟨both.2, both.1⟩)
  | trans a b c first second ih₁ ih₂ =>
    rcases ih₁ with equal | both
    · rcases ih₂ with last | last
      · exact Or.inl (equal.trans last)
      · exact Or.inr ⟨equal.symm ▸ last.1, last.2⟩
    · rcases ih₂ with last | last
      · exact Or.inr ⟨both.1, last ▸ both.2⟩
      · exact Or.inr ⟨both.1, last.2⟩

theorem forgetCuts_fiber_eq_or_boundary {small large : Set C.Seam} (inclusion : small ⊆ large)
    (x y : C.Realization small) (equal : C.forgetCuts inclusion x = C.forgetCuts inclusion y) :
    x = y ∨ (x ∈ C.bankBoundary small ∧ y ∈ C.bankBoundary small) := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue small) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue small) y
  change MetricGluing.point C.Cell (C.glue large) a =
    MetricGluing.point C.Cell (C.glue large) b at equal
  exact C.eq_or_bankBoundary_of_eqvGen ((C.point_eq_iff large a b).mp equal)

def forgetCutsBoundaryQuotient {small large : Set C.Seam} (inclusion : small ⊆ large) :
    BoundaryQuotient (C.Realization small) (C.Realization large) where
  projection := ⟨C.forgetCuts inclusion, (C.forgetCuts_lipschitz inclusion).continuous⟩
  quotient := Topology.IsQuotientMap.of_surjective_continuous (C.forgetCuts_surjective inclusion)
    (C.forgetCuts_lipschitz inclusion).continuous
  boundary := C.bankBoundary small
  fibers := C.forgetCuts_fiber_eq_or_boundary inclusion

/-- Restoring cuts is a homeomorphism away from the bank boundary and its image. -/
def forgetCutsComplementHomeomorph {small large : Set C.Seam} (inclusion : small ⊆ large) :
    ↥((C.bankBoundary small)ᶜ) ≃ₜ
      ↥((C.forgetCuts inclusion '' C.bankBoundary small)ᶜ) :=
  (C.forgetCutsBoundaryQuotient inclusion).complementHomeomorph (C.isClosed_bankBoundary small)

@[simp] theorem forgetCutsComplementHomeomorph_apply {small large : Set C.Seam}
    (inclusion : small ⊆ large) (x : ↥((C.bankBoundary small)ᶜ)) :
    (C.forgetCutsComplementHomeomorph inclusion x).val = C.forgetCuts inclusion x.val := rfl

end Unfoldings.TriangleComplex
