module

public import Unfoldings.Complex.FaceRoutes
public import Unfoldings.Complex.PointSeamRoute

/-!
# Resolving actual geodesic face-route junctions into bounded seam paths

Every piece has actual tagged entry and exit points. At a junction their
face tags may differ by several seams, including at flat subdivision
vertices. The constructed point-fiber path connects those actual copies
using fewer seams than the original face count. No generic-crossing premise
or perturbation of the geodesic is required.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.FaceRoute

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {a b : C.Realization Set.univ} {p : Path a b} (R : C.FaceRoute p)

def entry (i : Fin R.steps) : C.Cell (R.face i) :=
  Classical.choose (R.inside i (R.time i.castSucc)
    ⟨le_rfl, (R.increasing Fin.castSucc_lt_succ).le⟩)

def exit (i : Fin R.steps) : C.Cell (R.face i) :=
  Classical.choose (R.inside i (R.time i.succ)
    ⟨(R.increasing Fin.castSucc_lt_succ).le, le_rfl⟩)

theorem entry_image (i : Fin R.steps) :
    C.faceMap Set.univ (R.face i) (R.entry i) = p (R.time i.castSucc) :=
  Classical.choose_spec (R.inside i (R.time i.castSucc)
    ⟨le_rfl, (R.increasing Fin.castSucc_lt_succ).le⟩)

theorem exit_image (i : Fin R.steps) :
    C.faceMap Set.univ (R.face i) (R.exit i) = p (R.time i.succ) :=
  Classical.choose_spec (R.inside i (R.time i.succ)
    ⟨(R.increasing Fin.castSucc_lt_succ).le, le_rfl⟩)

def junctionLeft (i : Fin R.steps) : C.PointFiber Set.univ (p (R.time i.succ)) :=
  ⟨⟨R.face i, R.exit i⟩, R.exit_image i⟩

def junctionRight (i j : Fin R.steps) (next : j.val = i.val + 1) :
    C.PointFiber Set.univ (p (R.time i.succ)) :=
  ⟨⟨R.face j, R.entry j⟩,
    (R.entry_image j).trans (congrArg p (congrArg R.time (Fin.ext next)))⟩

end Unfoldings.TriangleComplex.FaceRoute

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F

theorem exists_short_faceRoute_junction {a b : C.Realization Set.univ} {p : Path a b}
    (R : C.FaceRoute p) (i j : Fin R.steps) (next : j.val = i.val + 1) :
    ∃ W : C.PointSeamRoute Set.univ (p (R.time i.succ))
      (R.junctionLeft i) (R.junctionRight i j next), W.steps < Fintype.card Face :=
  F.exists_short_pointSeamRoute Set.univ _ _ _

end Unfoldings.SpatialFolding
