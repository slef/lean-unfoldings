module

public import Unfoldings.Complex

/-!
# Boundary edges and the two banks of a cut seam

Boundary banks are local edges with no retained pairing. They have canonical
nonexpanding maps to the cut realization. Restoring a seam identifies its two
banks pointwise. The bank labels are distinct even for a seam joining two edges
of the same triangle. This does not assert that boundary vertices have distinct
metric images: other retained seams may still join their endpoints.

Identifying these edges with the boundary of a topological manifold requires
the later vertex-link and local-chart theorems.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A local edge occurs on one side of the given seam. -/
def Incident (s : C.Seam) (e : EdgeRef Face) : Prop := e = C.left s ∨ e = C.right s

/-- A local edge is a boundary bank when no retained seam pairs it. -/
def IsBoundaryEdge (retain : Set C.Seam) (e : EdgeRef Face) : Prop :=
  ¬ ∃ s ∈ retain, C.Incident s e

/-- Cutting more seams preserves every existing boundary edge. -/
theorem isBoundaryEdge_antitone {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain')
    {e : EdgeRef Face} (boundary : C.IsBoundaryEdge retain' e) : C.IsBoundaryEdge retain e := by
  rintro ⟨s, hs, incident⟩
  exact boundary ⟨s, inclusion hs, incident⟩

@[simp] theorem isBoundaryEdge_empty (e : EdgeRef Face) : C.IsBoundaryEdge ∅ e := by
  simp [IsBoundaryEdge]

@[simp] theorem isBoundaryEdge_left_iff (retain : Set C.Seam) (s : C.Seam) :
    C.IsBoundaryEdge retain (C.left s) ↔ s ∉ retain := by
  constructor
  · intro boundary hs
    exact boundary ⟨s, hs, Or.inl rfl⟩
  · rintro hs ⟨t, ht, incident⟩
    have same : s = t := C.unique s t (incident.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact hs (same.symm ▸ ht)

@[simp] theorem isBoundaryEdge_right_iff (retain : Set C.Seam) (s : C.Seam) :
    C.IsBoundaryEdge retain (C.right s) ↔ s ∉ retain := by
  constructor
  · intro boundary hs
    exact boundary ⟨s, hs, Or.inr rfl⟩
  · rintro hs ⟨t, ht, incident⟩
    have same : s = t := C.unique s t
      (incident.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h))))
    exact hs (same.symm ▸ ht)

/-- Original unpaired edges remain boundary edges under every cutting choice. -/
theorem isBoundaryEdge_of_unpaired {e : EdgeRef Face}
    (unpaired : ∀ s, ¬ C.Incident s e) (retain : Set C.Seam) : C.IsBoundaryEdge retain e := by
  rintro ⟨s, _, incident⟩
  exact unpaired s incident

/-- Boundary labels keep the original face and edge, rather than their spatial image. -/
abbrev BoundaryBank (retain : Set C.Seam) := {e : EdgeRef Face // C.IsBoundaryEdge retain e}

def leftBank (retain : Set C.Seam) (s : C.Seam) (cut : s ∉ retain) : C.BoundaryBank retain :=
  ⟨C.left s, (C.isBoundaryEdge_left_iff retain s).mpr cut⟩

def rightBank (retain : Set C.Seam) (s : C.Seam) (cut : s ∉ retain) : C.BoundaryBank retain :=
  ⟨C.right s, (C.isBoundaryEdge_right_iff retain s).mpr cut⟩

/-- Every cut seam has two distinct local bank labels. -/
theorem leftBank_ne_rightBank (retain : Set C.Seam) (s : C.Seam) (cut : s ∉ retain) :
    C.leftBank retain s cut ≠ C.rightBank retain s cut := by
  intro equal
  exact C.distinct s (congrArg Subtype.val equal)

/-- Map an entire bank, including its endpoints, to the cut realization. -/
def bankMap (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    (C.triangle bank.val.face).Edge bank.val.edge → C.Realization retain :=
  C.faceMap retain bank.val.face ∘ (C.triangle bank.val.face).edgeMap bank.val.edge

theorem bankMap_lipschitz (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    LipschitzWith 1 (C.bankMap retain bank) := by
  simpa [bankMap] using (C.faceMap_lipschitz retain bank.val.face).comp
    ((C.triangle bank.val.face).edgeMap_isometry bank.val.edge).lipschitzWith

/-- Restoring a cut seam identifies its two banks by the original edge isometry. -/
theorem forgetCuts_banks {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain')
    (s : C.Seam) (cut : s ∉ retain) (restored : s ∈ retain')
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    C.forgetCuts inclusion (C.bankMap retain (C.leftBank retain s cut) x) =
      C.forgetCuts inclusion (C.bankMap retain (C.rightBank retain s cut) (C.identify s x)) := by
  exact C.seam_identified retain' s restored x

end Unfoldings.TriangleComplex
