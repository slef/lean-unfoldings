module

public import Unfoldings.Complex

/-! Restrict a triangle complex to selected whole faces with inherited seam identifications. -/

@[expose] public section

noncomputable section


namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
def restrictFaces (U : Set Face) : TriangleComplex.{u, v} {f : Face // f ∈ U} := by
  classical
  exact {
    triangle := fun f => C.triangle f.val
    Seam := {s : C.Seam // (C.left s).face ∈ U ∧ (C.right s).face ∈ U}
    left := fun s => ⟨⟨(C.left s.val).face, s.property.1⟩, (C.left s.val).edge⟩
    right := fun s => ⟨⟨(C.right s.val).face, s.property.2⟩, (C.right s.val).edge⟩
    distinct := fun s equal => C.distinct s.val
      (congrArg (fun e => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) equal)
    identify := fun s => C.identify s.val
    unique := fun s t shared => Subtype.ext (C.unique s.val t.val
      (shared.imp
        (fun equal => congrArg (fun e => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) equal)
        (fun shared => shared.imp
          (fun equal => congrArg (fun e => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) equal)
          (fun shared => shared.imp
            (fun equal => congrArg (fun e => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) equal)
            (fun equal => congrArg (fun e => (⟨e.face.val, e.edge⟩ : EdgeRef Face)) equal))))) }

open Classical in
def restrictRetain (U : Set Face) (retain : Set C.Seam) : Set (C.restrictFaces U).Seam :=
  {s | s.val ∈ retain}

end Unfoldings.TriangleComplex

