module

public import Unfoldings.Development.SubdivisionNonoverlap
public import Unfoldings.Development.NonoverlapNormalization

/-! Any actual development of a connected conforming refinement decides coarse nonoverlap. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {FineC : TriangleComplex.{w, z} Child}
  {retain : Set C.Seam} {fineRetain : Set FineC.Seam}
  (E : FacewiseDevelopment C retain) (S : C.Subdivision FineC)
  (H : S.Conforming retain fineRetain) (A : FacewiseDevelopment FineC fineRetain)

include S H

theorem refinement_nonoverlapping_iff (connected : FineC.DuallyConnected fineRetain) :
    A.Nonoverlapping ↔ E.Nonoverlapping := by
  classical
  by_cases present : Nonempty Child
  · exact (A.nonoverlapping_iff_of_duallyConnected (E.subdivide S H) connected
      (Classical.choice present)).trans (E.subdivide_nonoverlapping_iff S H)
  · have empty : (E.subdivide S H).Nonoverlapping := by
      intro f _ _
      exact (present ⟨f⟩).elim
    exact ⟨fun _ => E.nonoverlapping_of_subdivide S H empty, fun _ f _ _ => (present ⟨f⟩).elim⟩

theorem refinement_nonoverlapping_iff_of_preconnected [PreconnectedSpace (C.Realization retain)] :
    A.Nonoverlapping ↔ E.Nonoverlapping := by
  let : PreconnectedSpace (FineC.Realization fineRetain) :=
    H.metricEquiv.symm.surjective.denseRange.preconnectedSpace H.metricEquiv.symm.continuous
  exact E.refinement_nonoverlapping_iff S H A (FineC.duallyConnected_of_preconnected fineRetain)

end Unfoldings.FacewiseDevelopment
